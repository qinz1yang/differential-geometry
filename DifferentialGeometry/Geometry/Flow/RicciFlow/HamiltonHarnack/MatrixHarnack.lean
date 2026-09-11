import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.ShiControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.AncientLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.SlabExhaustion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Regularity.Joint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.NonnegativeCurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.RankOneSupport
import DifferentialGeometry.Geometry.Connection.ChartBridge.Metric.InverseGram
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Restriction
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling
import DifferentialGeometry.Tensor.Alternating.Bundle.Defs
import DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private theorem tensor0SFamily_chartBasis_eval_continuousOn
    {s : Nat} {K : Set Real}
    {A : (t : Real) → (x : M) → Tensor0SSpace s I x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    (alpha : M) (idx : Fin s → Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun q : {t : Real // t ∈ K} × M =>
        A q.1.1 q.2
          (fun k => chartBasisVecFiber (I := I) alpha (idx k) q.2))
      {q : {t : Real // t ∈ K} × M |
        q.2 ∈ (trivializationAt E (TangentSpace I) alpha).baseSet} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let P := {q : {t : Real // t ∈ K} × M //
    q.2 ∈ (trivializationAt E (TangentSpace I) alpha).baseSet}
  have hslot : ∀ k : Fin s, Continuous
      (fun p : P =>
        Bundle.TotalSpace.mk' E p.1.2
          (chartBasisVecFiber (I := I) alpha (idx k) p.1.2)) := by
    intro k
    exact (chartBasisVec_contMDiffOn (I := I) alpha (idx k)).continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun p => p.2)
  exact hA.eval_continuous
    (P := P) (τ := fun p => p.1.1.1) (b := fun p => p.1.2)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    (fun p => p.1.1.2)
    (continuous_snd.comp continuous_subtype_val) hslot

private theorem chartInvGramMatrix_family_continuousOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {K : Set Real} (hK : K ⊆ D.regular) (alpha : M)
    (i j : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun q : {t : Real // t ∈ K} × M =>
        chartInvGramMatrix (I := I) (G.metric q.1.1) alpha q.2 i j)
      {q : {t : Real // t ∈ K} × M |
        q.2 ∈ chartLeviCivitaGoodSet (I := I) alpha} := by
  have hincl : ContinuousOn
      (fun q : {t : Real // t ∈ K} × M =>
        ((q.1 : Real), extChartAt I alpha q.2))
      {q : {t : Real // t ∈ K} × M |
        q.2 ∈ chartLeviCivitaGoodSet (I := I) alpha} :=
    (continuous_subtype_val.comp continuous_fst).continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) alpha).comp
        continuous_snd.continuousOn (fun q hq =>
          chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq))
  have hraw := MetricFamilySmoothOn.chartInvGramOnE_continuousOn
    (I := I) hG hK alpha i j
  refine (hraw.comp hincl (fun q hq =>
    ⟨q.1.2, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq⟩)).congr ?_
  intro q hq
  change (chartInvGramMatrix (I := I) (G.metric q.1.1) alpha q.2) i j =
    chartInvGramOnE (I := I) (G.metric q.1.1) alpha i j
      (extChartAt I alpha q.2)
  rw [chartInvGramOnE_def,
    (extChartAt I alpha).left_inv
      (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq)]

private theorem chartInvGramMatrix_family_comp_continuous
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {K : Set Real} (hK : K ⊆ D.regular) (alpha : M)
    {P : Type*} [TopologicalSpace P]
    (pull : P → {t : Real // t ∈ K} × M) (hpull : Continuous pull)
    (hgood : ∀ q, (pull q).2 ∈ chartLeviCivitaGoodSet (I := I) alpha)
    (i j : Fin (Module.finrank Real E)) :
    Continuous
      (fun q : P =>
        chartInvGramMatrix (I := I) (G.metric (pull q).1.1)
          alpha (pull q).2 i j) :=
  (chartInvGramMatrix_family_continuousOn
    (I := I) hG hK alpha i j).comp_continuous hpull hgood

private theorem exists_isCompact_superset_quadratic_level_local
    {ZModel : Type*} [NormedAddCommGroup ZModel] [NormedSpace Real ZModel]
    [FiniteDimensional Real ZModel] [Nontrivial ZModel]
    {Z : M → Type*} [∀ x, AddCommGroup (Z x)] [∀ x, Module Real (Z x)]
    [∀ x, TopologicalSpace (Z x)]
    [TopologicalSpace (Bundle.TotalSpace ZModel Z)]
    [FiberBundle ZModel Z]
    [T2Space M]
    (q : Bundle.TotalSpace ZModel Z → Real)
    (hqcont : Continuous q)
    (hqpos : ∀ p : Bundle.TotalSpace ZModel Z, p.2 ≠ 0 → 0 < q p)
    (hqsmul : ∀ (x : M) (c : Real) (z : Z x),
      q (Bundle.TotalSpace.mk' ZModel x (c • z)) =
        c ^ 2 * q (Bundle.TotalSpace.mk' ZModel x z))
    {C : Set M} (hC : IsCompact C)
    (e : Bundle.Trivialization ZModel
      (Bundle.TotalSpace.proj (F := ZModel) (E := Z)))
    [e.IsLinear Real]
    (hCe : C ⊆ e.baseSet) :
    ∃ L : Set (Bundle.TotalSpace ZModel Z),
      IsCompact L ∧ {p | p.proj ∈ C ∧ q p = 1} ⊆ L := by
  rcases C.eq_empty_or_nonempty with hCempty | hCne
  · subst C
    refine ⟨∅, isCompact_empty, ?_⟩
    simp
  let mkSymm : M × ZModel → Bundle.TotalSpace ZModel Z := fun z =>
    Bundle.TotalSpace.mk' ZModel z.1 (e.symmL Real z.1 z.2)
  let qCoord : M × ZModel → Real := fun z => q (mkSymm z)
  have hmkSymm : ContinuousOn mkSymm (e.baseSet ×ˢ Set.univ) := by
    refine e.continuousOn_symm.congr ?_
    intro z hz
    change (Bundle.TotalSpace.mk' ZModel z.1 (e.symmL Real z.1 z.2) :
        Bundle.TotalSpace ZModel Z) =
      Bundle.TotalSpace.mk' ZModel z.1 (e.symm z.1 z.2)
    refine Bundle.TotalSpace.ext rfl ?_
    exact heq_of_eq (e.symmL_apply hz.1 z.2)
  have hqCoord : ContinuousOn qCoord (e.baseSet ×ˢ Set.univ) :=
    hqcont.comp_continuousOn hmkSymm
  let sphere : Set ZModel := Metric.sphere (0 : ZModel) 1
  let unitDomain : Set (M × ZModel) := C ×ˢ sphere
  have hSphereCompact : IsCompact sphere := isCompact_sphere 0 1
  have hSphereNonempty : sphere.Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hUnitCompact : IsCompact unitDomain := hC.prod hSphereCompact
  have hUnitNonempty : unitDomain.Nonempty := hCne.prod hSphereNonempty
  have hUnitSub : unitDomain ⊆ e.baseSet ×ˢ Set.univ :=
    Set.prod_mono hCe (Set.subset_univ sphere)
  obtain ⟨z₀, hz₀, hz₀min⟩ :=
    hUnitCompact.exists_isMinOn hUnitNonempty (hqCoord.mono hUnitSub)
  let m : Real := qCoord z₀
  have hz₀norm : ‖z₀.2‖ = 1 := by
    simpa [unitDomain, sphere, Metric.mem_sphere] using hz₀.2
  have hz₀ne : z₀.2 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz₀norm
    norm_num at hz₀norm
  have hsymmNe : e.symmL Real z₀.1 z₀.2 ≠ 0 := by
    intro hzero
    apply hz₀ne
    calc
      z₀.2 = e.continuousLinearMapAt Real z₀.1
          (e.symmL Real z₀.1 z₀.2) :=
        (e.continuousLinearMapAt_symmL (hCe hz₀.1) z₀.2).symm
      _ = 0 := by rw [hzero, map_zero]
  have hm : 0 < m := by
    change 0 < qCoord z₀
    exact hqpos (mkSymm z₀) hsymmNe
  let R : Real := max 1 m⁻¹
  have hbound : ∀ y v, y ∈ C → qCoord (y, v) = 1 → ‖v‖ ≤ R := by
    intro y v hy hlevel
    have hv : v ≠ 0 := by
      intro hv
      subst v
      have hqzero : qCoord (y, 0) = 0 := by
        change q (Bundle.TotalSpace.mk' ZModel y
          (e.symmL Real y (0 : ZModel))) = 0
        rw [map_zero]
        have h := hqsmul y 0 (0 : Z y)
        simpa using h
      rw [hqzero] at hlevel
      norm_num at hlevel
    have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let u : ZModel := ‖v‖⁻¹ • v
    have hunorm : ‖u‖ = 1 := by
      simp [u, norm_smul, hvnorm]
    have huSphere : u ∈ sphere := by
      simpa [sphere, Metric.mem_sphere] using hunorm
    have hyu : (y, u) ∈ unitDomain := ⟨hy, huSphere⟩
    have hscale : qCoord (y, u) = ‖v‖⁻¹ ^ 2 * qCoord (y, v) := by
      change q (Bundle.TotalSpace.mk' ZModel y (e.symmL Real y u)) = _
      rw [show e.symmL Real y u = ‖v‖⁻¹ • e.symmL Real y v by
        simp [u], hqsmul]
    have hmin : m ≤ ‖v‖⁻¹ ^ 2 := by
      have h := hz₀min hyu
      change m ≤ qCoord (y, u) at h
      rw [hscale, hlevel, mul_one] at h
      exact h
    have hmul : ‖v‖ ^ 2 * m ≤ ‖v‖ ^ 2 * ‖v‖⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_left hmin (sq_nonneg ‖v‖)
    have hcancel : ‖v‖ ^ 2 * ‖v‖⁻¹ ^ 2 = 1 := by
      field_simp
    have hnormSqMul : ‖v‖ ^ 2 * m ≤ 1 := hmul.trans_eq hcancel
    have hnormSq : ‖v‖ ^ 2 ≤ m⁻¹ := by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ hm).2 (by simpa [mul_comm] using hnormSqMul)
    by_cases hvone : ‖v‖ ≤ 1
    · exact hvone.trans (le_max_left 1 m⁻¹)
    · calc
        ‖v‖ ≤ ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
        _ ≤ m⁻¹ := hnormSq
        _ ≤ R := le_max_right 1 m⁻¹
  let ambient : Set (M × ZModel) := C ×ˢ Metric.closedBall 0 R
  have hAmbientCompact : IsCompact ambient :=
    hC.prod (isCompact_closedBall 0 R)
  have hAmbientSub : ambient ⊆ e.baseSet ×ˢ Set.univ :=
    Set.prod_mono hCe (Set.subset_univ _)
  let T : Set (M × ZModel) := {z ∈ ambient | qCoord z = 1}
  have hTClosed : IsClosed T :=
    hAmbientCompact.isClosed.isClosed_eq
      (hqCoord.mono hAmbientSub) continuousOn_const
  have hTCompact : IsCompact T :=
    hAmbientCompact.of_isClosed_subset hTClosed fun _ hz => hz.1
  let L : Set (Bundle.TotalSpace ZModel Z) := mkSymm '' T
  have hTSub : T ⊆ e.baseSet ×ˢ Set.univ := fun _ hz =>
    hAmbientSub hz.1
  have hLCompact : IsCompact L :=
    hTCompact.image_of_continuousOn (hmkSymm.mono hTSub)
  refine ⟨L, hLCompact, ?_⟩
  intro p hp
  have hpbase : p.proj ∈ e.baseSet := hCe hp.1
  let z : M × ZModel := (p.proj, (e p).2)
  have hmkz : mkSymm z = p := by
    change (Bundle.TotalSpace.mk' ZModel p.proj
        (e.symmL Real p.proj (e p).2) : Bundle.TotalSpace ZModel Z) = p
    refine Bundle.TotalSpace.ext rfl ?_
    exact heq_of_eq (by
      rw [e.symmL_apply hpbase, e.symm_proj_apply p hpbase])
  have hqz : qCoord z = 1 := by
    change q (mkSymm z) = 1
    rw [hmkz]
    exact hp.2
  have hzT : z ∈ T := by
    refine ⟨⟨hp.1, ?_⟩, hqz⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbound p.proj (e p).2 hp.1 hqz
  exact ⟨z, hzT, hmkz⟩

private theorem quadratic_level_isCompact
    {ZModel : Type*} [NormedAddCommGroup ZModel] [NormedSpace Real ZModel]
    [FiniteDimensional Real ZModel] [Nontrivial ZModel]
    {Z : M → Type*} [∀ x, AddCommGroup (Z x)] [∀ x, Module Real (Z x)]
    [∀ x, TopologicalSpace (Z x)]
    [TopologicalSpace (Bundle.TotalSpace ZModel Z)]
    [FiberBundle ZModel Z] [VectorBundle Real ZModel Z]
    [T2Space M] [LocallyCompactSpace M]
    (q : Bundle.TotalSpace ZModel Z → Real)
    (hqcont : Continuous q)
    (hqpos : ∀ p : Bundle.TotalSpace ZModel Z, p.2 ≠ 0 → 0 < q p)
    (hqsmul : ∀ (x : M) (c : Real) (z : Z x),
      q (Bundle.TotalSpace.mk' ZModel x (c • z)) =
        c ^ 2 * q (Bundle.TotalSpace.mk' ZModel x z))
    {K : Set M} (hK : IsCompact K) :
    IsCompact {p : Bundle.TotalSpace ZModel Z | p.proj ∈ K ∧ q p = 1} := by
  let e (x : M) := trivializationAt ZModel Z x
  have hxbase : ∀ x : M, x ∈ (e x).baseSet := fun x =>
    FiberBundle.mem_baseSet_trivializationAt' x
  choose C hCcompact hxC hCe using fun x : M =>
    exists_compact_subset (e x).open_baseSet (hxbase x)
  have hlocal : ∀ x : M, ∃ L : Set (Bundle.TotalSpace ZModel Z),
      IsCompact L ∧ {p | p.proj ∈ C x ∧ q p = 1} ⊆ L := by
    intro x
    exact exists_isCompact_superset_quadratic_level_local
      q hqcont hqpos hqsmul (hCcompact x) (e x) (hCe x)
  choose L hLcompact hLsup using hlocal
  obtain ⟨t, _, hKt⟩ := hK.elim_nhds_subcover
    (fun x => interior (C x)) (fun x _ => isOpen_interior.mem_nhds (hxC x))
  let Lall : Set (Bundle.TotalSpace ZModel Z) := ⋃ x ∈ t, L x
  have hLallCompact : IsCompact Lall :=
    t.isCompact_biUnion fun x _ => hLcompact x
  have hsub : {p : Bundle.TotalSpace ZModel Z | p.proj ∈ K ∧ q p = 1} ⊆ Lall := by
    intro p hp
    obtain ⟨x, hxt, hpx⟩ := Set.mem_iUnion₂.mp (hKt hp.1)
    exact Set.mem_iUnion₂.mpr ⟨x, hxt,
      hLsup x ⟨interior_subset hpx, hp.2⟩⟩
  have hbaseClosed : IsClosed {p : Bundle.TotalSpace ZModel Z | p.proj ∈ K} :=
    hK.isClosed.preimage (FiberBundle.continuous_proj ZModel Z)
  have hlevelClosed : IsClosed {p : Bundle.TotalSpace ZModel Z | q p = 1} :=
    isClosed_eq hqcont continuous_const
  exact hLallCompact.of_isClosed_subset (hbaseClosed.inter hlevelClosed) hsub

abbrev HarnackCarrierModel :=
  HamiltonHarnackTwoForm E × Tensor0SModel 1 Real E

abbrev HarnackCarrierFiber (x : M) :=
  HamiltonHarnackTwoForm (TangentSpace I x) × Tensor0SSpace 1 I x

abbrev HarnackCarrierTotal :=
  Bundle.TotalSpace (HarnackCarrierModel (E := E))
    (HarnackCarrierFiber (E := E) (I := I) (M := M))

noncomputable instance harnackTwoFormModelFiniteDimensional :
    FiniteDimensional Real (HamiltonHarnackTwoForm E) := by
  let _ : FiniteDimensional Real
      (ContinuousMultilinearMap Real (fun _ : Fin 2 ↦ E) Real) :=
    DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_finiteDimensional 2
  exact FiniteDimensional.of_injective
    ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

theorem harnackCarrierModel_finrank_pos
    [NeZero (Module.finrank Real E)] :
    0 < Module.finrank Real (HarnackCarrierModel (E := E)) := by
  rw [Module.finrank_prod,
    DifferentialGeometry.Tensor.Multilinear.finrank_continuousMultilinearMap]
  have hE : 0 < Module.finrank Real E :=
    Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))
  simpa [pow_one] using
    Nat.add_pos_right (Module.finrank Real (HamiltonHarnackTwoForm E)) hE

theorem harnackCarrierModel_nontrivial
    [NeZero (Module.finrank Real E)] :
    Nontrivial (HarnackCarrierModel (E := E)) :=
  Module.nontrivial_of_finrank_pos (R := Real)
    harnackCarrierModel_finrank_pos

private abbrev HarnackTwoFormTotal :=
  Bundle.TotalSpace (HamiltonHarnackTwoForm E)
    (fun x : M => HamiltonHarnackTwoForm (TangentSpace I x))

private def harnackTwoFormToTensorTotal
    (p : HarnackTwoFormTotal (E := E) (I := I) (M := M)) :
    Bundle.TotalSpace (Tensor0SModel 2 Real E)
      (fun x : M => Tensor0SSpace 2 I x) :=
  Bundle.TotalSpace.mk' (Tensor0SModel 2 Real E) p.proj
    (HamiltonHarnackTwoForm.toTensor0S (I := I) p.2)

private theorem harnackTwoFormToTensorTotal_continuous :
    Continuous
      (harnackTwoFormToTensorTotal (E := E) (I := I) (M := M)) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  rw [FiberBundle.continuousAt_totalSpace]
  constructor
  · exact (FiberBundle.continuous_proj (HamiltonHarnackTwoForm E)
      (fun x : M => HamiltonHarnackTwoForm (TangentSpace I x))).continuousAt
  · let ea := trivializationAt (HamiltonHarnackTwoForm E)
      (fun x : M => HamiltonHarnackTwoForm (TangentSpace I x)) p₀.proj
    let et := trivializationAt (Tensor0SModel 2 Real E)
      (fun x : M => Tensor0SSpace 2 I x) p₀.proj
    have hea : ContinuousAt
        (fun p : HarnackTwoFormTotal (E := E) (I := I) (M := M) =>
          (ea p).2) p₀ := by
      exact (FiberBundle.continuousAt_totalSpace (HamiltonHarnackTwoForm E)
        (fun p : HarnackTwoFormTotal (E := E) (I := I) (M := M) => p)).1
          continuousAt_id |>.2
    have heq :
        (fun p : HarnackTwoFormTotal (E := E) (I := I) (M := M) =>
          (et (harnackTwoFormToTensorTotal
            (E := E) (I := I) (M := M) p)).2) =
        fun p => (ea p).2.toContinuousMultilinearMap := by
      funext p
      ext v
      change HamiltonHarnackTwoForm.toTensor0S (I := I) p.2
          (fun i => (trivializationAt E (TangentSpace I : M → Type _) p₀.proj).symmL
            Real p.proj (v i)) = _
      change p.2 (fun i =>
          (trivializationAt E (TangentSpace I : M → Type _) p₀.proj).symmL
            Real p.proj (v i)) = _
      have heaApply :=
        FiberBundle.trivializationAt_continuousAlternatingMap_apply
          (F₁ := E) (E₁ := (TangentSpace I : M → Type _))
          (F₂ := Real) (E₂ := Bundle.Trivial M Real)
          p₀.proj p
      change ea p = _ at heaApply
      rw [congrArg Prod.snd heaApply]
      simp [ContinuousAlternatingMap.inCoordinates]
      congr 1
    change ContinuousAt
      (fun p : HarnackTwoFormTotal (E := E) (I := I) (M := M) =>
        (et (harnackTwoFormToTensorTotal
          (E := E) (I := I) (M := M) p)).2) p₀
    rw [heq]
    exact ContinuousAlternatingMap.continuous_toContinuousMultilinearMap.continuousAt.comp hea

private theorem harnackCarrier_first_continuous :
    Continuous
      (fun p : HarnackCarrierTotal (E := E) (I := I) (M := M) =>
        (Bundle.TotalSpace.mk' (HamiltonHarnackTwoForm E) p.proj p.2.1 :
          HarnackTwoFormTotal (E := E) (I := I) (M := M))) := by
  have hdiag := FiberBundle.Prod.isInducing_diag
    (HamiltonHarnackTwoForm E)
    (fun x : M => HamiltonHarnackTwoForm (TangentSpace I x))
    (Tensor0SModel 1 Real E) (fun x : M => Tensor0SSpace 1 I x)
  exact continuous_fst.comp hdiag.continuous

private theorem harnackCarrier_second_continuous :
    Continuous
      (fun p : HarnackCarrierTotal (E := E) (I := I) (M := M) =>
        (Bundle.TotalSpace.mk' (Tensor0SModel 1 Real E) p.proj p.2.2 :
          Bundle.TotalSpace (Tensor0SModel 1 Real E)
            (fun x : M => Tensor0SSpace 1 I x))) := by
  have hdiag := FiberBundle.Prod.isInducing_diag
    (HamiltonHarnackTwoForm E)
    (fun x : M => HamiltonHarnackTwoForm (TangentSpace I x))
    (Tensor0SModel 1 Real E) (fun x : M => Tensor0SSpace 1 I x)
  exact continuous_snd.comp hdiag.continuous

def harnackCarrierNormSq
    (g : SmoothRiemannianMetric I M)
    (p : HarnackCarrierTotal (E := E) (I := I) (M := M)) : Real :=
  normSq0S (I := I) g p.proj 2 p.2.1.toTensor0S +
    normSq0S (I := I) g p.proj 1 p.2.2

theorem harnackCarrierNormSq_continuous
    (g : SmoothRiemannianMetric I M) :
    Continuous (harnackCarrierNormSq (E := E) (I := I) (M := M) g) := by
  have hq2 := (normSq0S_total_cont (I := I) (M := M) (s := 2) g).comp
    (harnackTwoFormToTensorTotal_continuous.comp
      harnackCarrier_first_continuous)
  have hq1 := (normSq0S_total_cont (I := I) (M := M) (s := 1) g).comp
    harnackCarrier_second_continuous
  exact hq2.add hq1

omit [FiniteDimensional Real E] in
private theorem harnackTwoForm_toTensor0S_ne_zero
    {x : M} {U : HamiltonHarnackTwoForm (TangentSpace I x)}
    (hU : U ≠ 0) :
    U.toTensor0S ≠ 0 := by
  intro hzero
  apply hU
  apply HamiltonHarnackTwoForm.toTensor0S_injective (I := I)
  rw [hzero]
  have h := HamiltonHarnackTwoForm.toTensor0S_smul
    (I := I) (M := M) (x := x) 0 U
  simpa using h.symm

theorem harnackCarrierNormSq_pos
    (g : SmoothRiemannianMetric I M)
    (p : HarnackCarrierTotal (E := E) (I := I) (M := M))
    (hp : p.2 ≠ 0) :
    0 < harnackCarrierNormSq (E := E) (I := I) (M := M) g p := by
  by_cases hfirst : p.2.1 = 0
  · have hsecond : p.2.2 ≠ 0 := by
      intro hsecond
      apply hp
      ext <;> simp_all
    exact add_pos_of_nonneg_of_pos
      (normSq0S_nonneg (I := I) g p.proj 2 p.2.1.toTensor0S)
      ((tensor0SMetricData (I := I) g p.proj 1).inner_pos_of_ne_zero hsecond)
  · exact add_pos_of_pos_of_nonneg
      ((tensor0SMetricData (I := I) g p.proj 2).inner_pos_of_ne_zero
        (harnackTwoForm_toTensor0S_ne_zero (I := I) hfirst))
      (normSq0S_nonneg (I := I) g p.proj 1 p.2.2)

theorem harnackCarrierNormSq_smul
    (g : SmoothRiemannianMetric I M) (x : M) (c : Real)
    (z : HarnackCarrierFiber (E := E) (I := I) (M := M) x) :
    harnackCarrierNormSq (E := E) (I := I) (M := M) g
        (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x (c • z)) =
      c ^ 2 * harnackCarrierNormSq (E := E) (I := I) (M := M) g
        (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x z) := by
  change normSq0S (I := I) g x 2 (c • z.1).toTensor0S +
      normSq0S (I := I) g x 1 (c • z.2) =
    c ^ 2 * (normSq0S (I := I) g x 2 z.1.toTensor0S +
      normSq0S (I := I) g x 1 z.2)
  rw [HamiltonHarnackTwoForm.toTensor0S_smul]
  have h2 := Tensor0SBundle.normSq0S_smul (I := I) g c z.1.toTensor0S
  have h1 := Tensor0SBundle.normSq0S_smul (I := I) g c z.2
  rw [h2, h1]
  ring

theorem harnackCarrierNormSq_level_isCompact
    [NeZero (Module.finrank Real E)] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {K : Set M} (hK : IsCompact K) :
    IsCompact
      {p : HarnackCarrierTotal (E := E) (I := I) (M := M) |
        p.proj ∈ K ∧
          harnackCarrierNormSq (E := E) (I := I) (M := M) g p = 1} := by
  let _ : Nontrivial (HarnackCarrierModel (E := E)) :=
    harnackCarrierModel_nontrivial
  let _ : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional I
  exact quadratic_level_isCompact
    (harnackCarrierNormSq (E := E) (I := I) (M := M) g)
    (harnackCarrierNormSq_continuous (E := E) (I := I) (M := M) g)
    (harnackCarrierNormSq_pos (E := E) (I := I) (M := M) g)
    (harnackCarrierNormSq_smul (E := E) (I := I) (M := M) g)
    hK

theorem harnackCarrierNormSq_time_level_isCompact
    [NeZero (Module.finrank Real E)] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {T : Set Real} (hT : IsCompact T)
    {K : Set M} (hK : IsCompact K) :
    IsCompact
      {q : {t : Real // t ∈ T} ×
          HarnackCarrierTotal (E := E) (I := I) (M := M) |
        q.2.proj ∈ K ∧
          harnackCarrierNormSq (E := E) (I := I) (M := M) g q.2 = 1} := by
  let : CompactSpace {t : Real // t ∈ T} :=
    isCompact_iff_compactSpace.mp hT
  have hcarrier := harnackCarrierNormSq_level_isCompact
    (E := E) (I := I) (M := M) g hK
  have hprod : IsCompact
      ((Set.univ : Set {t : Real // t ∈ T}) ×ˢ
        {p : HarnackCarrierTotal (E := E) (I := I) (M := M) |
          p.proj ∈ K ∧
            harnackCarrierNormSq (E := E) (I := I) (M := M) g p = 1}) :=
    isCompact_univ.prod hcarrier
  convert hprod using 1
  ext q
  simp

variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
private theorem hamiltonPAt_family_continuous [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {K : Set Real} (hK : K ⊆ D.regular) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 3 K
      (fun t x => hamiltonPAt (I := I) (S.family.metric t) x) := by
  have hnabla := (nablaRicci_cont (I := I) S hS).mono hK
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun alpha => (trivializationAt E (TangentSpace I) alpha).baseSet)
    (hN := fun alpha => (trivializationAt E (TangentSpace I) alpha).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) alpha))
  intro alpha idx
  have hmain := tensor0SFamily_chartBasis_eval_continuousOn
    (I := I) hnabla alpha idx
  have hswap := tensor0SFamily_chartBasis_eval_continuousOn
    (I := I) hnabla alpha (fun k => idx ((Equiv.swap (0 : Fin 3) 1) k))
  refine (hmain.sub hswap).congr ?_
  intro q _
  simp only [hamiltonPAt, hamiltonP, Tensor0SSpace.sub_apply,
    Tensor0SSpace.domDomCongr_apply]
  simp [metricNablaRic, SolutionFamily.connection, SolutionFamily.ricci,
    SolutionOn.ricci, SolutionOn.family, metricCov, metricRicci]

omit [SigmaCompactSpace M] in
private theorem hamiltonMAt_origin_family_continuous [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (origin : Real) {K : Set Real}
    (hK : K ⊆ D.regular) (horigin : ∀ t ∈ K, origin < t) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x =>
        hamiltonMbarAt (I := I) (S.family.metric t) x +
          (1 / (2 * (t - origin)) : Real) •
            metricRicci (I := I) (M := M) (S.family.metric t) x) := by
  classical
  have hnabla2 := (nabla2Ricci_cont (I := I) S hS).mono hK
  have hKcarrier : K ⊆ D.carrier := fun _ ht => D.regular_subset (hK ht)
  have hric := hS.ricciCont.mono hKcarrier
  have hrm := hS.rm04Cont.mono hKcarrier
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun alpha => chartLeviCivitaGoodSet (I := I) alpha)
    (hN := fun alpha => (chartLeviCivitaGoodSet_isOpen (I := I) alpha).mem_nhds
      (self_mem_chartLeviCivitaGoodSet (I := I) (α := alpha)))
  intro alpha idx
  let U : Set ({t : Real // t ∈ K} × M) :=
    {q | q.2 ∈ chartLeviCivitaGoodSet (I := I) alpha}
  have hgoodBase : U ⊆
      {q : {t : Real // t ∈ K} × M |
        q.2 ∈ (trivializationAt E (TangentSpace I) alpha).baseSet} := by
    intro q hq
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hq
  have hn2 (a b c d : Fin (Module.finrank Real E)) : ContinuousOn
      (fun q : {t : Real // t ∈ K} × M =>
        metricNabla2Ric (I := I) (M := M) (S.family.metric q.1.1) q.2
          ![chartBasisVecFiber (I := I) alpha a q.2,
            chartBasisVecFiber (I := I) alpha b q.2,
            chartBasisVecFiber (I := I) alpha c q.2,
            chartBasisVecFiber (I := I) alpha d q.2]) U := by
    refine ((tensor0SFamily_chartBasis_eval_continuousOn
      (I := I) hnabla2 alpha ![a, b, c, d]).mono hgoodBase).congr ?_
    intro q _
    change
      metricNabla2Ric (I := I) (M := M) (S.family.metric q.1.1) q.2
          ![chartBasisVecFiber (I := I) alpha a q.2,
            chartBasisVecFiber (I := I) alpha b q.2,
            chartBasisVecFiber (I := I) alpha c q.2,
            chartBasisVecFiber (I := I) alpha d q.2] =
        metricNabla2Ric (I := I) (M := M) (S.family.metric q.1.1) q.2
          (fun k => chartBasisVecFiber (I := I) alpha (![a, b, c, d] k) q.2)
    apply congrArg
    funext k
    fin_cases k <;> rfl
  have hricComp (a b : Fin (Module.finrank Real E)) : ContinuousOn
      (fun q : {t : Real // t ∈ K} × M =>
        metricRicci (I := I) (M := M) (S.family.metric q.1.1) q.2
          ![chartBasisVecFiber (I := I) alpha a q.2,
            chartBasisVecFiber (I := I) alpha b q.2]) U := by
    refine ((tensor0SFamily_chartBasis_eval_continuousOn
      (I := I) hric alpha ![a, b]).mono hgoodBase).congr ?_
    intro q _
    simp only [SolutionOn.ricci, SolutionFamily.ricci]
    change
      metricRicci (I := I) (M := M) (S.family.metric q.1.1) q.2
          ![chartBasisVecFiber (I := I) alpha a q.2,
            chartBasisVecFiber (I := I) alpha b q.2] =
        metricRicci (I := I) (M := M) (S.family.metric q.1.1) q.2
          (fun k => chartBasisVecFiber (I := I) alpha (![a, b] k) q.2)
    apply congrArg
    funext k
    fin_cases k <;> rfl
  have hrmComp (a b c d : Fin (Module.finrank Real E)) : ContinuousOn
      (fun q : {t : Real // t ∈ K} × M =>
        metricRm04 (I := I) (M := M) (S.family.metric q.1.1) q.2
          ![chartBasisVecFiber (I := I) alpha a q.2,
            chartBasisVecFiber (I := I) alpha b q.2,
            chartBasisVecFiber (I := I) alpha c q.2,
            chartBasisVecFiber (I := I) alpha d q.2]) U := by
    refine ((tensor0SFamily_chartBasis_eval_continuousOn
      (I := I) hrm alpha ![a, b, c, d]).mono hgoodBase).congr ?_
    intro q _
    simp only [SolutionOn.family, SolutionFamily.rm04]
    change
      metricRm04 (I := I) (M := M) (S.family.metric q.1.1) q.2
          ![chartBasisVecFiber (I := I) alpha a q.2,
            chartBasisVecFiber (I := I) alpha b q.2,
            chartBasisVecFiber (I := I) alpha c q.2,
            chartBasisVecFiber (I := I) alpha d q.2] =
        metricRm04 (I := I) (M := M) (S.family.metric q.1.1) q.2
          (fun k => chartBasisVecFiber (I := I) alpha (![a, b, c, d] k) q.2)
    apply congrArg
    funext k
    fin_cases k <;> rfl
  have hinv (i j : Fin (Module.finrank Real E)) : ContinuousOn
      (fun q : {t : Real // t ∈ K} × M =>
        (chartInvGramMatrix (I := I) (S.family.metric q.1.1) alpha q.2) i j) U := by
    simpa only [U] using chartInvGramMatrix_family_continuousOn
      (I := I) (G := S.family) hS.smoothMetric hK alpha i j
  have htime : Continuous
      (fun q : {t : Real // t ∈ K} × M => (q.1 : Real)) :=
    continuous_subtype_val.comp continuous_fst
  have helapsed : Continuous
      (fun q : {t : Real // t ∈ K} × M => (q.1 : Real) - origin) :=
    htime.sub continuous_const
  have hden : Continuous
      (fun q : {t : Real // t ∈ K} × M => 2 * ((q.1 : Real) - origin)) :=
    continuous_const.mul helapsed
  have hden_ne : ∀ q : {t : Real // t ∈ K} × M,
      2 * ((q.1 : Real) - origin) ≠ 0 := by
    intro q
    exact mul_ne_zero (by norm_num)
      (ne_of_gt (sub_pos.mpr (horigin q.1.1 q.1.2)))
  have hshift : Continuous
      (fun q : {t : Real // t ∈ K} × M =>
        1 / (2 * ((q.1 : Real) - origin))) :=
    continuous_const.div hden hden_ne
  have hfirst : ContinuousOn
      (fun q : {t : Real // t ∈ K} × M =>
        ∑ i, ∑ j,
          (chartInvGramMatrix (I := I) (S.family.metric q.1.1)
              alpha q.2) i j *
            metricNabla2Ric (I := I) (M := M) (S.family.metric q.1.1) q.2
              ![chartBasisVecFiber (I := I) alpha i q.2,
                chartBasisVecFiber (I := I) alpha j q.2,
                chartBasisVecFiber (I := I) alpha (idx 0) q.2,
                chartBasisVecFiber (I := I) alpha (idx 1) q.2]) U := by
    exact continuousOn_finsetSum Finset.univ fun i _ =>
      continuousOn_finsetSum Finset.univ fun j _ =>
      (hinv i j).mul (hn2 i j (idx 0) (idx 1))
  have hsecond : ContinuousOn
      (fun q : {t : Real // t ∈ K} × M =>
        ∑ i, ∑ j,
          (chartInvGramMatrix (I := I) (S.family.metric q.1.1)
              alpha q.2) i j *
            metricNabla2Ric (I := I) (M := M) (S.family.metric q.1.1) q.2
              ![chartBasisVecFiber (I := I) alpha i q.2,
                chartBasisVecFiber (I := I) alpha (idx 0) q.2,
                chartBasisVecFiber (I := I) alpha (idx 1) q.2,
                chartBasisVecFiber (I := I) alpha j q.2]) U := by
    exact continuousOn_finsetSum Finset.univ fun i _ =>
      continuousOn_finsetSum Finset.univ fun j _ =>
      (hinv i j).mul (hn2 i (idx 0) (idx 1) j)
  have hcurv : ContinuousOn
      (fun q : {t : Real // t ∈ K} × M =>
        ∑ i, ∑ j,
          (chartInvGramMatrix (I := I) (S.family.metric q.1.1)
              alpha q.2) i j *
            (∑ k, ∑ l,
              (chartInvGramMatrix (I := I) (S.family.metric q.1.1)
                  alpha q.2) k l *
                (metricRm04 (I := I) (M := M) (S.family.metric q.1.1) q.2
                    ![chartBasisVecFiber (I := I) alpha (idx 0) q.2,
                      chartBasisVecFiber (I := I) alpha k q.2,
                      chartBasisVecFiber (I := I) alpha i q.2,
                      chartBasisVecFiber (I := I) alpha (idx 1) q.2] *
                  metricRicci (I := I) (M := M) (S.family.metric q.1.1) q.2
                    ![chartBasisVecFiber (I := I) alpha l q.2,
                      chartBasisVecFiber (I := I) alpha j q.2]))) U := by
    exact continuousOn_finsetSum Finset.univ fun i _ =>
      continuousOn_finsetSum Finset.univ fun j _ =>
        (hinv i j).mul (continuousOn_finsetSum Finset.univ fun k _ =>
          continuousOn_finsetSum Finset.univ fun l _ =>
            (hinv k l).mul
              ((hrmComp (idx 0) k i (idx 1)).mul (hricComp l j)))
  have hformulaCont := ((hfirst.sub hsecond).add hcurv).add
    (hshift.continuousOn.mul (hricComp (idx 0) (idx 1)))
  refine hformulaCont.congr ?_
  intro q hq
  have hxbase : q.2 ∈ (trivializationAt E (TangentSpace I) alpha).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hq
  let basis := chartBasisFamily (I := I) alpha hxbase
  let clock : HarnackClock := ⟨origin, q.1.1, horigin q.1.1 q.1.2⟩
  have hinverse : MetricInverseInBasis (I := I)
      (S.family.metric q.1.1) q.2 basis
      (fun i j => (chartInvGramMatrix (I := I)
        (S.family.metric q.1.1) alpha q.2) i j) := by
    simpa only [basis] using chartInvGram_inverse
      (I := I) (S.family.metric q.1.1) alpha hxbase
  have hformula := hamiltonMAt_apply_basis
    (I := I) S hS clock (hK q.1.2) q.2 basis
      (fun i j => (chartInvGramMatrix (I := I)
      (S.family.metric q.1.1) alpha q.2) i j)
      hinverse (idx 0) (idx 1)
  have hvec2 (A B : TangentSpace I q.2) : vec2 A B = ![A, B] := by
    funext k
    fin_cases k <;> rfl
  have hvec4 (A B C D : TangentSpace I q.2) :
      vec4 A B C D = ![A, B, C, D] := by
    funext k
    fin_cases k <;> rfl
  simp_rw [hvec2, hvec4] at hformula
  have hslots :
      (fun k : Fin 2 => chartBasisVecFiber (I := I) alpha (idx k) q.2) =
        ![basis (idx 0), basis (idx 1)] := by
    funext k
    fin_cases k <;> simp [basis, chartBasisFamily_apply]
  have hM :
      hamiltonMbarAt (I := I) (S.family.metric q.1.1) q.2 +
          (1 / (2 * (q.1.1 - origin)) : Real) •
            metricRicci (I := I) (M := M) (S.family.metric q.1.1) q.2 =
        hamiltonMAt (I := I) clock (S.family.metric q.1.1) q.2 := by
    simp [hamiltonMAt, clock, HarnackClock.elapsed]
  change
    (hamiltonMbarAt (I := I) (S.family.metric q.1.1) q.2 +
        (1 / (2 * (q.1.1 - origin)) : Real) •
          metricRicci (I := I) (M := M) (S.family.metric q.1.1) q.2)
      (fun k => chartBasisVecFiber (I := I) alpha (idx k) q.2) = _
  rw [hM, hslots]
  simpa [clock, HarnackClock.elapsed, basis, chartBasisFamily_apply]
    using hformula

noncomputable def hamiltonHarnackQuadraticAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) : Real :=
  hamiltonQuadraticAt (S.base.metric clock.time)
    ⟨S.base.rm04 clock.time x,
      DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric clock.time) x⟩
    (hamiltonPAt (I := I) (S.base.metric clock.time) x)
    (hamiltonMAt (I := I) clock (S.base.metric clock.time) x) U W

noncomputable def hamiltonUnshiftedHarnackQuadraticAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) : Real :=
  hamiltonQuadraticAt (S.base.metric t)
    ⟨S.base.rm04 t x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩
    (hamiltonPAt (I := I) (S.base.metric t) x)
    (hamiltonMbarAt (I := I) (S.base.metric t) x) U W

omit [SigmaCompactSpace M] in
theorem hamiltonHarnackQuadraticAt_eq_unshifted_add
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) :
    hamiltonHarnackQuadraticAt (I := I) S clock x U W =
      hamiltonUnshiftedHarnackQuadraticAt (I := I) S clock.time x U W +
        inner0S (I := I) (S.base.metric clock.time) x 2
            (metricRicci (I := I) (M := M) (S.base.metric clock.time) x)
            (W.product W) / (2 * clock.elapsed) := by
  unfold hamiltonHarnackQuadraticAt hamiltonUnshiftedHarnackQuadraticAt
  unfold hamiltonQuadraticAt hamiltonMAt
  rw [inner0S_add_left, _root_.Tensor0SBundle.inner0S_smul_left]
  ring

omit [SigmaCompactSpace M] in
theorem hamiltonHarnackQuadraticAt_eq_hamiltonBlockQuadratic
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x)
    {A : Type*} [Fintype A] [DecidableEq A]
    (basis : Module.Basis A Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I)
      (S.base.metric clock.time) x basis (identityInvMetric (Idx := A))) :
    hamiltonHarnackQuadraticAt (I := I) S clock x U W =
      hamiltonBlockQuadratic
        (fun a b c d => tensor04StandardAt (I := I) (M := M)
          (S.base.rm04 clock.time x) (basis a) (basis b) (basis d) (basis c))
        (fun a b c => hamiltonPAt (I := I)
          (S.base.metric clock.time) x ![basis a, basis b, basis c])
        (fun a b => hamiltonMAt (I := I) clock
          (S.base.metric clock.time) x ![basis a, basis b])
        (fun a b => U ![basis a, basis b])
        (fun a => W ![basis a]) := by
  unfold hamiltonHarnackQuadraticAt
  exact hamiltonQuadraticAt_eq_hamiltonBlockQuadratic
    (S.base.metric clock.time)
    ⟨S.base.rm04 clock.time x,
      DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric clock.time) x⟩
    (hamiltonPAt (I := I) (S.base.metric clock.time) x)
    (hamiltonMAt (I := I) clock (S.base.metric clock.time) x)
    U W basis hinv

omit [SigmaCompactSpace M] in
private def hamiltonPerturbedHarnackQuadraticAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (phi psi : Real) (x : M)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) : Real :=
  hamiltonHarnackQuadraticAt (I := I) S clock x U W +
    (phi / clock.elapsed) *
      normSq0S (I := I) (S.base.metric clock.time) x 1 W +
    psi * normSq0S (I := I) (S.base.metric clock.time) x 2 U.toTensor0S

private noncomputable def hamiltonMField
    (clock : HarnackClock) (g : SmoothRiemannianMetric I M) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  hamiltonMOriginField (I := I) clock.origin clock.time g

private noncomputable def hamiltonKField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 t)

private noncomputable def hamiltonMFamilyField
    (origin t : Real) (g : SmoothRiemannianMetric I M) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  hamiltonMOriginField (I := I) origin t g

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem hamiltonMFamilyField_eq_hamiltonMField
    (clock : HarnackClock) (g : SmoothRiemannianMetric I M) :
    hamiltonMFamilyField (I := I) clock.origin clock.time g =
      hamiltonMField (I := I) clock g := by
  rfl

omit [SigmaCompactSpace M] in
private theorem hamiltonMFamilyField_apply
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (origin : Real) {t : Real} (ht : t ∈ D.regular) (x : M) :
    hamiltonMFamilyField (I := I) origin t (S.base.metric t) x =
      hamiltonMbarAt (I := I) (S.base.metric t) x +
        (1 / (2 * (t - origin)) : Real) •
          metricRicci (I := I) (M := M) (S.base.metric t) x := by
  rw [hamiltonMFamilyField, hamiltonMOriginField_apply]
  have hbar :
      hamiltonDivPAt (I := I) (S.base.metric t) x +
          hamiltonCurvatureRicciAt (I := I) (S.base.metric t) x =
        hamiltonMbarAt (I := I) (S.base.metric t) x := by
    simpa only [SolutionOn.family] using
      (hamiltonMbarAt_eq_hamiltonDivPAt_add
        (I := I) S hS ⟨t, ht⟩ x).symm
  rw [hbar]

omit [SigmaCompactSpace M] in
private theorem hamiltonMField_apply
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M) :
    hamiltonMField (I := I) clock (S.base.metric clock.time) x =
      hamiltonMAt (I := I) clock (S.base.metric clock.time) x := by
  rw [hamiltonMField, hamiltonMOriginField_apply]
  exact (hamiltonMAt_eq_hamiltonDivPAt_add (I := I) S hS clock ht x).symm

omit [CompleteSpace E] [FiniteDimensional Real E] [SigmaCompactSpace M]
  [T2Space M] [IsManifold I ∞ M] in
private theorem sub_mul_hasDerivWithinAt_of_continuousWithinAt
    {s : Set Real} {t : Real} {f : Real → Real}
    (hf : ContinuousWithinAt f s t) :
    HasDerivWithinAt (fun r : Real => (r - t) * f r) (f t) s t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have ht : Filter.Tendsto f (nhdsWithin t (s \ {t})) (nhds (f t)) :=
    hf.mono_left (nhdsWithin_mono t Set.sdiff_subset)
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrt : r ≠ t := hr.2
  have hsub : r - t ≠ 0 := sub_ne_zero.mpr hrt
  simp only [slope, sub_self, zero_mul, vsub_eq_sub, sub_zero, smul_eq_mul]
  field_simp [hsub]

omit [CompleteSpace E] [FiniteDimensional Real E] [SigmaCompactSpace M]
  [T2Space M] [IsManifold I ∞ M] in
private theorem sub_sq_mul_hasDerivWithinAt_zero_of_continuousWithinAt
    {s : Set Real} {t : Real} {f : Real → Real}
    (hf : ContinuousWithinAt f s t) :
    HasDerivWithinAt (fun r : Real => ((r - t) * (r - t)) * f r) 0 s t := by
  have hlinear := sub_mul_hasDerivWithinAt_of_continuousWithinAt
    (s := s) (t := t) hf
  simpa only [sub_self, zero_mul, mul_assoc] using
    sub_mul_hasDerivWithinAt_of_continuousWithinAt hlinear.continuousWithinAt

omit [CompleteSpace E] [FiniteDimensional Real E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem tensor02At_hasDerivWithinAt_of_affine_slots
    {x : M} {s : Set Real} {t : Real}
    (T : Real → Tensor02At (I := I) (M := M) x)
    (A B RA RB : TangentSpace I x) (d : Real)
    (hT : ∀ X Y : TangentSpace I x,
      ContinuousWithinAt
        (fun r : Real => T r (vec2 (I := I) X Y)) s t)
    (hmove : HasDerivWithinAt
      (fun r : Real => T r
        (vec2 (I := I) (A + (r - t) • RA) (B + (r - t) • RB))) d s t) :
    HasDerivWithinAt
      (fun r : Real => T r (vec2 (I := I) A B))
      (d - T t (vec2 (I := I) RA B) - T t (vec2 (I := I) A RB)) s t := by
  have hexp :
      (fun r : Real => T r
        (vec2 (I := I) (A + (r - t) • RA) (B + (r - t) • RB))) =
      fun r : Real =>
        T r (vec2 (I := I) A B) +
          (r - t) * T r (vec2 (I := I) RA B) +
          (r - t) * T r (vec2 (I := I) A RB) +
          ((r - t) * (r - t)) * T r (vec2 (I := I) RA RB) := by
    funext r
    have hfirst (X Y Z : TangentSpace I x) :
        T r (vec2 (I := I) (X + (r - t) • Y) Z) =
          T r (vec2 (I := I) X Z) +
            (r - t) * T r (vec2 (I := I) Y Z) := by
      let base : Fin 2 → TangentSpace I x := vec2 (I := I) X Z
      have hslot : vec2 (I := I) (X + (r - t) • Y) Z =
          Function.update base (0 : Fin 2) (X + (r - t) • Y) := by
        funext q
        fin_cases q <;> simp [base, vec2, Function.update]
      rw [hslot, (T r).map_update_add, (T r).map_update_smul]
      congr 2 <;> congr 1 <;> funext q <;>
        fin_cases q <;> simp [base, vec2, Function.update]
    have hsecond (X Y Z : TangentSpace I x) :
        T r (vec2 (I := I) X (Y + (r - t) • Z)) =
          T r (vec2 (I := I) X Y) +
            (r - t) * T r (vec2 (I := I) X Z) := by
      let base : Fin 2 → TangentSpace I x := vec2 (I := I) X Y
      have hslot : vec2 (I := I) X (Y + (r - t) • Z) =
          Function.update base (1 : Fin 2) (Y + (r - t) • Z) := by
        funext q
        fin_cases q <;> simp [base, vec2, Function.update]
      rw [hslot, (T r).map_update_add, (T r).map_update_smul]
      congr 2 <;> congr 1 <;> funext q <;>
        fin_cases q <;> simp [base, vec2, Function.update]
    calc
      T r (vec2 (I := I) (A + (r - t) • RA) (B + (r - t) • RB)) =
          T r (vec2 (I := I) A (B + (r - t) • RB)) +
            (r - t) * T r (vec2 (I := I) RA (B + (r - t) • RB)) :=
        hfirst A RA (B + (r - t) • RB)
      _ = _ := by rw [hsecond A B RB, hsecond RA B RB]; ring
  have hRA := sub_mul_hasDerivWithinAt_of_continuousWithinAt (hT RA B)
  have hRB := sub_mul_hasDerivWithinAt_of_continuousWithinAt (hT A RB)
  have hquad := sub_sq_mul_hasDerivWithinAt_zero_of_continuousWithinAt (hT RA RB)
  rw [hexp] at hmove
  have hfixed : HasDerivWithinAt
      (fun r : Real => T r (vec2 (I := I) A B))
      (d - T t (vec2 (I := I) RA B) - T t (vec2 (I := I) A RB) - 0) s t := by
    apply (((hmove.sub hRA).sub hRB).sub hquad).congr
    · intro r _
      simp only [Pi.sub_apply]
      ring
    · simp only [Pi.sub_apply]
      ring
  exact hfixed.congr_deriv (by ring)

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackQuadraticAt_eq_inner
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (phi psi : Real) (x : M)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) :
    hamiltonPerturbedHarnackQuadraticAt (I := I) S clock phi psi x U W =
      inner0S (I := I) (S.base.metric clock.time) x 4
          ((S.base.rm04 clock.time x).domDomCongr curvatureSlotSwap)
          (U.toTensor0S.product U.toTensor0S) +
        2 * inner0S (I := I) (S.base.metric clock.time) x 3
          (hamiltonPField (I := I) (S.base.metric clock.time) x)
          (U.toTensor0S.product W) +
        inner0S (I := I) (S.base.metric clock.time) x 2
          (hamiltonMField (I := I) clock (S.base.metric clock.time) x)
          (W.product W) +
        (phi / clock.elapsed) *
          inner0S (I := I) (S.base.metric clock.time) x 1 W W +
        psi * inner0S (I := I) (S.base.metric clock.time) x 2
          U.toTensor0S U.toTensor0S := by
  rw [hamiltonPerturbedHarnackQuadraticAt]
  unfold hamiltonHarnackQuadraticAt hamiltonQuadraticAt curvatureBlock
  rw [hamiltonPField_apply, hamiltonMField_apply S hS clock ht]
  rfl

omit [SigmaCompactSpace M] in
theorem hamiltonHarnackQuadraticAt_smul
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M) (c : Real)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) :
    hamiltonHarnackQuadraticAt (I := I) S clock x (c • U) (c • W) =
      c ^ 2 * hamiltonHarnackQuadraticAt (I := I) S clock x U W := by
  have hUU :
      (c • U).toTensor0S.product (c • U).toTensor0S =
        c ^ 2 • U.toTensor0S.product U.toTensor0S := by
    ext v
    simp only [Tensor0SSpace.product_apply,
      HamiltonHarnackTwoForm.toTensor0S_smul, Tensor0SSpace.smul_apply,
      HamiltonHarnackTwoForm.toTensor0S_apply, smul_eq_mul]
    ring
  have hUW :
      (c • U).toTensor0S.product (c • W) =
        c ^ 2 • U.toTensor0S.product W := by
    ext v
    simp only [Tensor0SSpace.product_apply,
      HamiltonHarnackTwoForm.toTensor0S_smul, Tensor0SSpace.smul_apply,
      HamiltonHarnackTwoForm.toTensor0S_apply, smul_eq_mul]
    ring
  have hWW : (c • W).product (c • W) = c ^ 2 • W.product W := by
    ext v
    simp only [Tensor0SSpace.product_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
    ring
  unfold hamiltonHarnackQuadraticAt hamiltonQuadraticAt curvatureBlock
  rw [hUU, hUW, hWW]
  simp only [Tensor0SBundle.inner0S_smul_right]
  ring

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackQuadraticAt_smul
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (phi psi : Real) (x : M) (c : Real)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) :
    hamiltonPerturbedHarnackQuadraticAt (I := I) S clock phi psi x
        (c • U) (c • W) =
      c ^ 2 * hamiltonPerturbedHarnackQuadraticAt
        (I := I) S clock phi psi x U W := by
  unfold hamiltonPerturbedHarnackQuadraticAt
  rw [hamiltonHarnackQuadraticAt_smul]
  rw [HamiltonHarnackTwoForm.toTensor0S_smul]
  rw [Tensor0SBundle.normSq0S_smul, Tensor0SBundle.normSq0S_smul]
  ring

omit [CompleteSpace E] [SigmaCompactSpace M] in
def normalizeHarnackCarrier
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (z : HarnackCarrierFiber (E := E) (I := I) (M := M) x) :
    HarnackCarrierFiber (E := E) (I := I) (M := M) x := by
  classical
  exact if z = 0 then z else
    (Real.sqrt (harnackCarrierNormSq (E := E) (I := I) (M := M) gRef
      (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x z)))⁻¹ • z

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem normalizeHarnackCarrier_ne_zero
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (z : HarnackCarrierFiber (E := E) (I := I) (M := M) x)
    (hz : z ≠ 0) :
    normalizeHarnackCarrier (E := E) (I := I) (M := M) gRef x z ≠ 0 := by
  rw [normalizeHarnackCarrier, if_neg hz]
  have hq := harnackCarrierNormSq_pos (E := E) (I := I) (M := M) gRef
    (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x z) hz
  exact smul_ne_zero (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 hq))) hz

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem normalizeHarnackCarrier_normSq
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (z : HarnackCarrierFiber (E := E) (I := I) (M := M) x)
    (hz : z ≠ 0) :
    harnackCarrierNormSq (E := E) (I := I) (M := M) gRef
        (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x
          (normalizeHarnackCarrier (E := E) (I := I) (M := M) gRef x z)) = 1 := by
  let q := harnackCarrierNormSq (E := E) (I := I) (M := M) gRef
    (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x z)
  have hq : 0 < q :=
    harnackCarrierNormSq_pos (E := E) (I := I) (M := M) gRef
      (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x z) hz
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  rw [normalizeHarnackCarrier, if_neg hz]
  rw [harnackCarrierNormSq_smul]
  change (Real.sqrt q)⁻¹ ^ 2 * q = 1
  field_simp [ne_of_gt hsqrt]
  exact (Real.sq_sqrt hq.le).symm

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private def hamiltonPerturbedHarnackRayleigh
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (origin : Real) (phi : Real → M → Real) (psi : Real → Real)
    (gRef : SmoothRiemannianMetric I M)
    (t : Real) (x : M)
    (z : HarnackCarrierFiber (E := E) (I := I) (M := M) x) : Real := by
  classical
  exact if ht : origin < t then
    if z = 0 then 1 else
      hamiltonPerturbedHarnackQuadraticAt (I := I) S ⟨origin, t, ht⟩
        (phi t x) (psi t) x z.1 z.2 /
          harnackCarrierNormSq (E := E) (I := I) (M := M) gRef
            (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x z)
  else 1

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private def hamiltonPerturbedHarnackQuadraticValue
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (origin : Real) (phi : Real -> M -> Real) (psi : Real -> Real)
    (t : Real) (x : M)
    (z : HarnackCarrierFiber (E := E) (I := I) (M := M) x) : Real := by
  classical
  exact if ht : origin < t then
    if z = 0 then 1 else
      hamiltonPerturbedHarnackQuadraticAt (I := I) S ⟨origin, t, ht⟩
        (phi t x) (psi t) x z.1 z.2
  else 1

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackQuadraticValue_zero
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (origin : Real) (phi : Real -> M -> Real) (psi : Real -> Real)
    (t : Real) (x : M) :
    hamiltonPerturbedHarnackQuadraticValue
      (E := E) (I := I) (M := M) S origin phi psi t x 0 = 1 := by
  classical
  simp [hamiltonPerturbedHarnackQuadraticValue]

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (origin : Real) (phi : Real -> M -> Real) (psi : Real -> Real)
    (t : Real) (ht : origin < t) (x : M)
    (z : HarnackCarrierFiber (E := E) (I := I) (M := M) x)
    (hz : z ≠ 0) :
    hamiltonPerturbedHarnackQuadraticValue
        (E := E) (I := I) (M := M) S origin phi psi t x z =
      hamiltonPerturbedHarnackQuadraticAt (I := I) S ⟨origin, t, ht⟩
        (phi t x) (psi t) x z.1 z.2 := by
  classical
  simp only [hamiltonPerturbedHarnackQuadraticValue, dif_pos ht, if_neg hz]

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackRayleigh_zero
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (origin : Real) (phi : Real → M → Real) (psi : Real → Real)
    (gRef : SmoothRiemannianMetric I M) (t : Real) (x : M) :
    hamiltonPerturbedHarnackRayleigh (E := E) (I := I) (M := M)
      S origin phi psi gRef t x 0 = 1 := by
  classical
  simp [hamiltonPerturbedHarnackRayleigh]

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackRayleigh_normalize
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (origin : Real) (phi : Real → M → Real) (psi : Real → Real)
    (gRef : SmoothRiemannianMetric I M)
    (t : Real) (ht : origin < t) (x : M)
    (z : HarnackCarrierFiber (E := E) (I := I) (M := M) x)
    (hz : z ≠ 0) :
    hamiltonPerturbedHarnackRayleigh (E := E) (I := I) (M := M)
        S origin phi psi gRef t x
          (normalizeHarnackCarrier (E := E) (I := I) (M := M) gRef x z) =
      hamiltonPerturbedHarnackRayleigh (E := E) (I := I) (M := M)
        S origin phi psi gRef t x z := by
  let q := harnackCarrierNormSq (E := E) (I := I) (M := M) gRef
    (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x z)
  have hq : 0 < q :=
    harnackCarrierNormSq_pos (E := E) (I := I) (M := M) gRef
      (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x z) hz
  let c := (Real.sqrt q)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 hq))
  have hnorm :
      normalizeHarnackCarrier (E := E) (I := I) (M := M) gRef x z = c • z := by
    rw [normalizeHarnackCarrier, if_neg hz]
  have hcz : c • z ≠ 0 := smul_ne_zero hc hz
  classical
  simp only [hamiltonPerturbedHarnackRayleigh, dif_pos ht]
  rw [if_neg (normalizeHarnackCarrier_ne_zero
    (E := E) (I := I) (M := M) gRef x z hz), if_neg hz, hnorm]
  change
    hamiltonPerturbedHarnackQuadraticAt (I := I) S ⟨origin, t, ht⟩
          (phi t x) (psi t) x (c • z.1) (c • z.2) /
        harnackCarrierNormSq (E := E) (I := I) (M := M) gRef
          (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x (c • z)) = _
  rw [hamiltonPerturbedHarnackQuadraticAt_smul]
  rw [harnackCarrierNormSq_smul]
  change c ^ 2 * _ / (c ^ 2 * q) = _ / q
  field_simp [hc, ne_of_gt hq]

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackQuadraticAt_eq_block
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (phi psi : Real) (x : M)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x)
    {A : Type*} [Fintype A] [DecidableEq A]
    (basis : Module.Basis A Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I)
      (S.base.metric clock.time) x basis (identityInvMetric (Idx := A))) :
    hamiltonPerturbedHarnackQuadraticAt (I := I) S clock phi psi x U W =
      hamiltonBlockQuadratic
        (hamiltonPerturbedCurvatureBlock
          (fun a b c d => tensor04StandardAt (I := I) (M := M)
            (S.base.rm04 clock.time x) (basis a) (basis b) (basis d) (basis c))
          psi)
        (fun a b c => hamiltonPAt (I := I)
          (S.base.metric clock.time) x ![basis a, basis b, basis c])
        (hamiltonPerturbedMBlock clock
          (fun a b => hamiltonMAt (I := I) clock
            (S.base.metric clock.time) x ![basis a, basis b])
          phi)
        (fun a b => U ![basis a, basis b])
        (fun a => W ![basis a]) := by
  classical
  have hWnorm :
      normSq0S (I := I) (S.base.metric clock.time) x 1 W =
        ∑ a : A, (W ![basis a]) ^ 2 := by
    rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq
      (I := I) (S.base.metric clock.time) x 1 basis hinv W]
    rw [Tensor0SBundle.sum_fin_one_fun]
    apply Finset.sum_congr rfl
    intro a _
    simp only [component0S_apply]
    congr 1
    exact congrArg W (by
      funext i
      fin_cases i
      rfl)
  have hUnorm :
      normSq0S (I := I) (S.base.metric clock.time) x 2 U.toTensor0S =
        ∑ a : A, ∑ b : A, (U ![basis a, basis b]) ^ 2 := by
    rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq
      (I := I) (S.base.metric clock.time) x 2 basis hinv U.toTensor0S]
    rw [Tensor0SBundle.sum_fin_two_fun]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [component0S_apply, HamiltonHarnackTwoForm.toTensor0S_apply]
    congr 1
    exact congrArg U (by
      funext i
      fin_cases i <;> rfl)
  have hUskew : ∀ a b : A,
      U ![basis a, basis b] = -U ![basis b, basis a] := by
    intro a b
    calc
      U ![basis a, basis b] = U (fun i => basis (![a, b] i)) := by
        exact congrArg U (by funext i; fin_cases i <;> rfl)
      _ = -U (fun i => basis (![b, a] i)) := by
        simpa only [HamiltonHarnackTwoForm.component, component0S_apply,
          HamiltonHarnackTwoForm.toTensor0S_apply] using
            HamiltonHarnackTwoForm.component_skew (I := I) basis U a b
      _ = -U ![basis b, basis a] := by
        congr 1
        exact congrArg U (by funext i; fin_cases i <;> rfl)
  rw [hamiltonPerturbedBlockQuadratic_expand (hU := hUskew)]
  rw [← hamiltonHarnackQuadraticAt_eq_hamiltonBlockQuadratic
    (I := I) S clock x U W basis hinv]
  rw [← hWnorm, ← hUnorm]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonTensor0SOfComponents
    {A : Type*} [Fintype A] {s : Nat} {x : M}
    (basis : Module.Basis A Real (TangentSpace I x))
    (c : (Fin s -> A) -> Real) : Tensor0SSpace s I x :=
  (coordEquiv0S (I := I) basis s).symm c

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonTensor0SOfComponents_apply
    {A : Type*} [Fintype A] {s : Nat} {x : M}
    (basis : Module.Basis A Real (TangentSpace I x))
    (c : (Fin s -> A) -> Real) (slots : Fin s -> A) :
    hamiltonTensor0SOfComponents (I := I) basis c
        (fun i => basis (slots i)) = c slots := by
  change component0S (I := I) basis
    (hamiltonTensor0SOfComponents (I := I) basis c) slots = c slots
  rw [← coordEquiv0S_apply]
  simp [hamiltonTensor0SOfComponents]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonTensor0S_hasDerivAt_of_components
    {A : Type*} [Finite A]
    {s : Nat} {x : M} {t : Real}
    (basis : Module.Basis A Real (TangentSpace I x))
    (T : Real → Tensor0SSpace s I x) (Tdot : Tensor0SSpace s I x)
    (hT : ∀ slots : Fin s → A,
      HasDerivAt
        (fun r : Real => T r (fun i => basis (slots i)))
        (Tdot (fun i => basis (slots i))) t) :
    ∀ v : Fin s → TangentSpace I x,
      HasDerivAt (fun r : Real => T r v) (Tdot v) t := by
  classical
  let _ := Fintype.ofFinite A
  intro v
  have hfun :
      (fun r : Real => T r v) =
        fun r : Real =>
          ∑ slots : Fin s → A,
            T r (fun i => basis (slots i)) *
              ∏ i : Fin s, basis.coord (slots i) (v i) := by
    funext r
    rw [tensor0S_apply_eq_sum (I := I) basis (T r) v]
    refine Finset.sum_congr rfl fun slots _ => ?_
    rw [component0S_apply]
  rw [hfun]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun slots _ =>
    (hT slots).mul_const (∏ i : Fin s, basis.coord (slots i) (v i))
  refine hsum.congr_deriv ?_
  rw [tensor0S_apply_eq_sum (I := I) basis Tdot v]
  refine Finset.sum_congr rfl fun slots _ => ?_
  rw [component0S_apply]

omit [SigmaCompactSpace M] in
private theorem hamiltonKField_hasDerivAt
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D) (x : M)
    {A : Type*} [Fintype A] [DecidableEq A]
    (basis : Module.Basis A Real (TangentSpace I x))
    (horth : ∀ i j : A,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    let Kdot := hamiltonTensor0SOfComponents (I := I) basis
      (fun slots : Fin 4 → A =>
        let rmSlots := fun q : Fin 4 => slots (curvatureSlotSwap q)
        tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) basis
              (identityInvMetric (Idx := A))
              (nablaKRm04Field (I := I) S (t : Real) 2 x))
            (fun i => basis i) rmSlots +
          DifferentialGeometry.Geometry.Connection.hamiltonRmReact
            (fun q : Fin 4 → A =>
              S.base.rm04 (t : Real) x (fun p => basis (q p))) rmSlots)
    ∀ v : Fin 4 → TangentSpace I x,
      HasDerivAt
        (fun r : Real => hamiltonKField (I := I) S r x v)
        (Kdot v) (t : Real) := by
  dsimp only
  apply hamiltonTensor0S_hasDerivAt_of_components (I := I) basis
  intro slots
  let rmSlots := fun q : Fin 4 => slots (curvatureSlotSwap q)
  have hbase := rm04Base_of_solution_any
    (I := I) S hS t x basis horth rmSlots
  have hbaseAt := hbase.hasDerivAt (D.regular_mem_nhds t.2)
  simpa only [hamiltonKField, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply,
    hamiltonTensor0SOfComponents_apply, rmSlots] using hbaseAt

omit [SigmaCompactSpace M] in
private theorem hamiltonPField_hasDerivAt
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D) (x : M)
    {A : Type*} [Fintype A]
    (basis : Module.Basis A Real (TangentSpace I x)) :
    let Pdot := hamiltonTensor0SOfComponents (I := I) basis
      (fun slots : Fin 3 → A =>
        deriv (fun r : Real =>
          hamiltonPField (I := I) (S.base.metric r) x
            (fun i => basis (slots i))) (t : Real))
    ∀ v : Fin 3 → TangentSpace I x,
      HasDerivAt
        (fun r : Real => hamiltonPField (I := I) (S.base.metric r) x v)
        (Pdot v) (t : Real) := by
  dsimp only
  apply hamiltonTensor0S_hasDerivAt_of_components (I := I) basis
  intro slots
  have hwithin := hamiltonPAt_hasDerivWithinAt_of_ricci_flow
    (I := I) S hS t x (fun i => basis (slots i))
  have hAt := hwithin.hasDerivAt (D.regular_mem_nhds t.2)
  rw [hamiltonTensor0SOfComponents_apply]
  exact hAt.congr_deriv hAt.deriv.symm

omit [SigmaCompactSpace M] in
private theorem hamiltonMFamilyField_eval_continuousAt
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (X Y : TangentSpace I x) :
    ContinuousAt
      (fun r : Real =>
        hamiltonMFamilyField (I := I) clock.origin r
          (S.base.metric r) x (vec2 (I := I) X Y))
      clock.time := by
  let K : Set Real := D.regular ∩ Set.Ioi clock.origin
  have hclockK : clock.time ∈ K := ⟨ht, clock.origin_lt_time⟩
  have hKsub : K ⊆ D.regular := fun _ hr => hr.1
  have horigin : ∀ r ∈ K, clock.origin < r := fun _ hr => hr.2
  have hfamily := hamiltonMAt_origin_family_continuous
    (I := I) S hS clock.origin hKsub horigin
  have heval : Continuous
      (fun q : {r : Real // r ∈ K} =>
        (hamiltonMbarAt (I := I) (S.base.metric q.1) x +
          (1 / (2 * (q.1 - clock.origin)) : Real) •
            metricRicci (I := I) (M := M) (S.base.metric q.1) x)
          (vec2 (I := I) X Y)) := by
    apply hfamily.eval_continuous
      (P := {r : Real // r ∈ K}) (τ := Subtype.val) (b := fun _ => x)
    · exact continuous_subtype_val
    · exact fun q => q.2
    · exact continuous_const
    · intro i
      exact continuous_const
  have hrestrict : ContinuousAt
      (fun q : {r : Real // r ∈ K} =>
        hamiltonMFamilyField (I := I) clock.origin q.1
          (S.base.metric q.1) x (vec2 (I := I) X Y))
      ⟨clock.time, hclockK⟩ := by
    have heq :
        (fun q : {r : Real // r ∈ K} =>
          hamiltonMFamilyField (I := I) clock.origin q.1
            (S.base.metric q.1) x (vec2 (I := I) X Y)) =
        fun q : {r : Real // r ∈ K} =>
          (hamiltonMbarAt (I := I) (S.base.metric q.1) x +
            (1 / (2 * (q.1 - clock.origin)) : Real) •
              metricRicci (I := I) (M := M) (S.base.metric q.1) x)
            (vec2 (I := I) X Y) := by
      funext q
      rw [hamiltonMFamilyField_apply (I := I) S hS clock.origin q.2.1 x]
    rw [heq]
    exact heval.continuousAt
  have hwithin : ContinuousWithinAt
      (fun r : Real =>
        hamiltonMFamilyField (I := I) clock.origin r
          (S.base.metric r) x (vec2 (I := I) X Y))
      K clock.time :=
    (continuousWithinAt_iff_continuousAt_domRestrict _ hclockK).2 hrestrict
  have hKnhds : K ∈ nhds clock.time :=
    Filter.inter_mem (D.regular_isOpen.mem_nhds ht)
      (isOpen_Ioi.mem_nhds clock.origin_lt_time)
  exact (continuousWithinAt_iff_continuousAt hKnhds).1 hwithin

omit [SigmaCompactSpace M] in
private theorem hamiltonMFamilyField_hasDerivAt
    [I.Boundaryless]
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    let Mdot := hamiltonTensor0SOfComponents (I := I) basis
      (fun slots : Fin 2 → Fin n =>
        deriv (fun r : Real =>
          hamiltonMFamilyField (I := I) clock.origin r
            (S.base.metric r) x (fun i => basis (slots i))) clock.time)
    ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          hamiltonMFamilyField (I := I) clock.origin r
            (S.base.metric r) x v)
        (Mdot v) clock.time := by
  dsimp only
  apply hamiltonTensor0S_hasDerivAt_of_components (I := I) basis
  intro slots
  let Ric := metricRicci (I := I) (M := M)
    (S.base.metric clock.time) x
  let RicEnd := (ricciEndAt (I := I)
    (S.base.metric clock.time) Ric).toContinuousLinearMap
  let A := basis (slots 0)
  let B := basis (slots 1)
  let RA := RicEnd A
  let RB := RicEnd B
  have hmove := hamiltonMAt_hasDerivWithinAt_of_ricci_flow
    (I := I) S hS clock ht x basis horth (slots 0) (slots 1)
  dsimp only at hmove
  let moving : Real → Real := fun r =>
        hamiltonMFamilyField (I := I) clock.origin r
          (S.base.metric r) x
          (vec2 (I := I) (A + (r - clock.time) • RA)
            (B + (r - clock.time) • RB))
  have hmoveAt := hmove.hasDerivAt (D.regular_mem_nhds ht)
  have hmoveAt' : HasDerivAt moving (deriv moving clock.time) clock.time := by
    have hfun : moving = fun r : Real =>
        hamiltonDivPAt (I := I) (S.base.metric r) x
            (vec2 (I := I)
              (oneTimeUhlenbeckVector (I := I) (S.base.metric clock.time)
                clock.time r (basis (slots 0)))
              (oneTimeUhlenbeckVector (I := I) (S.base.metric clock.time)
                clock.time r (basis (slots 1)))) +
          hamiltonCurvatureRicciAt (I := I) (S.base.metric r) x
            (vec2 (I := I)
              (oneTimeUhlenbeckVector (I := I) (S.base.metric clock.time)
                clock.time r (basis (slots 0)))
              (oneTimeUhlenbeckVector (I := I) (S.base.metric clock.time)
                clock.time r (basis (slots 1)))) +
          (1 / (2 * (r - clock.origin))) *
            metricRicci (I := I) (M := M) (S.base.metric r) x
              (vec2 (I := I)
                (oneTimeUhlenbeckVector (I := I) (S.base.metric clock.time)
                  clock.time r (basis (slots 0)))
                (oneTimeUhlenbeckVector (I := I) (S.base.metric clock.time)
                  clock.time r (basis (slots 1)))) := by
      funext r
      simp only [moving, hamiltonMFamilyField, hamiltonMOriginField_apply,
        Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul,
        LinearMap.coe_toContinuousLinearMap',
        A, B, RA, RB, RicEnd, Ric, oneTimeUhlenbeckVector]
    rw [hfun]
    exact hmoveAt.congr_deriv hmoveAt.deriv.symm
  have hmove' : HasDerivWithinAt
      (fun r : Real =>
        hamiltonMFamilyField (I := I) clock.origin r
          (S.base.metric r) x
          (vec2 (I := I) (A + (r - clock.time) • RA)
            (B + (r - clock.time) • RB)))
      (deriv moving clock.time) Set.univ clock.time := by
    simpa only [moving] using hmoveAt'.hasDerivWithinAt
  have hfixed := tensor02At_hasDerivWithinAt_of_affine_slots
    (I := I) (s := Set.univ)
    (fun r : Real =>
      hamiltonMFamilyField (I := I) clock.origin r
        (S.base.metric r) x)
    A B RA RB (deriv moving clock.time)
    (fun X Y =>
      (hamiltonMFamilyField_eval_continuousAt
        (I := I) S hS clock ht x X Y).continuousWithinAt)
    hmove'
  have hAt := hfixed.hasDerivAt Filter.univ_mem
  rw [hamiltonTensor0SOfComponents_apply]
  have hslots : (fun i => basis (slots i)) = vec2 (I := I) A B := by
    funext i
    fin_cases i <;> rfl
  rw [hslots]
  exact hAt.congr_deriv hAt.deriv.symm

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonRmReact_add_ricci_slot_actions_matrix
    {Idx : Type*} [Fintype Idx]
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (hRm : Rm04Symm R)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (a b c d : Idx) :
    DifferentialGeometry.Geometry.Connection.hamiltonRmReact
        (fun q => R (q 0) (q 1) (q 2) (q 3)) ![a, b, c, d] +
        (∑ p : Idx, Ric a p * R p b c d) +
        (∑ p : Idx, Ric b p * R a p c d) +
        (∑ p : Idx, Ric c p * R a b p d) +
        (∑ p : Idx, Ric d p * R a b c p) =
      hamiltonRmReactionComponent R a b c d := by
  classical
  have htrace' (i j : Idx) : (∑ e : Idx, R i e j e) = -Ric i j := by
    calc
      (∑ e : Idx, R i e j e) = ∑ e : Idx, -R e i j e := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hRm.swap12]
      _ = -(∑ e : Idx, R e i j e) := by rw [Finset.sum_neg_distrib]
      _ = -Ric i j := by rw [hTrace]
  have hslot (i : Idx) (F : Idx -> Real) :
      (∑ e : Idx, ∑ f : Idx, R i e f e * F f) =
        -(∑ f : Idx, Ric i f * F f) := by
    calc
      (∑ e : Idx, ∑ f : Idx, R i e f e * F f) =
          ∑ f : Idx, ∑ e : Idx, R i e f e * F f := Finset.sum_comm
      _ = ∑ f : Idx, (∑ e : Idx, R i e f e) * F f := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.sum_mul]
      _ = -(∑ f : Idx, Ric i f * F f) := by
        simp only [htrace', neg_mul, Finset.sum_neg_distrib]
  unfold DifferentialGeometry.Geometry.Connection.hamiltonRmReact
    hamiltonRmReactionComponent hamiltonBComponent
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, neg_mul, sub_neg_eq_add]
  rw [hslot a (fun f => R f b c d), hslot b (fun f => R a f c d),
    hslot c (fun f => R a b f d), hslot d (fun f => R a b c f)]
  ring

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem ricciEnd_repr_orthonormal_matrix
    {x : M} {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (Ric : Tensor02At (I := I) (M := M) x) (i p : Idx) :
    basis.repr (ricciEndAt (I := I) g Ric (basis i)) p =
      Ric (vec2 (I := I) (basis i) (basis p)) := by
  classical
  let _ := Fintype.ofFinite Idx
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [basis_repr_eq_sum_inv_inner (I := I) g x basis
    (fun i j => if i = j then (1 : Real) else 0) hinv]
  simp only [ricciEnd_inner, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [SigmaCompactSpace M] in
private theorem hamiltonK_fixedHeat_component
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (hRm : Rm04Symm (fun a b c d =>
      S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))))
    (hTrace : curvatureRicciTraceComponents
      (fun a b c d => S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun a b => metricRicci (I := I) (M := M)
        (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis a) (basis b)))) :
    let Kdot := hamiltonTensor0SOfComponents (I := I) basis
      (fun slots : Fin 4 -> Fin n =>
        let rmSlots := fun q : Fin 4 => slots (curvatureSlotSwap q)
        tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) basis
              (identityInvMetric (Idx := Fin n))
              (nablaKRm04Field (I := I) S (t : Real) 2 x))
            (fun i => basis i) rmSlots +
          DifferentialGeometry.Geometry.Connection.hamiltonRmReact
            (fun q : Fin 4 -> Fin n =>
              S.base.rm04 (t : Real) x (fun p => basis (q p))) rmSlots)
    let nabla2K := Tensor0SField.domDomCongr ∞
      (frontExtendEquiv (frontExtendEquiv curvatureSlotSwap))
      (nablaKRm04Field (I := I) S (t : Real) 2)
    let roughK := metricTrace0S2TensorInBasis (I := I) basis
      (identityInvMetric (Idx := Fin n)) (nabla2K x)
    let Ric := metricRicci (I := I) (M := M)
      (S.base.metric (t : Real)) x
    let RicEnd := (ricciEndAt (I := I) (S.base.metric (t : Real)) Ric).toContinuousLinearMap
    ∀ a b c d,
      (Kdot - roughK + covariantEndomorphismAction0S (I := I)
          (hamiltonKField (I := I) S (t : Real) x) RicEnd)
          (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) =
        hamiltonRmReactionComponent
          (fun i j k l => S.base.rm04 (t : Real) x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
          a b d c := by
  classical
  dsimp only
  intro a b c d
  let R := fun i j k l => S.base.rm04 (t : Real) x
    (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))
  let Ric := metricRicci (I := I) (M := M)
    (S.base.metric (t : Real)) x
  let RicComp := fun i j => Ric (vec2 (I := I) (basis i) (basis j))
  let RicEnd := (ricciEndAt (I := I) (S.base.metric (t : Real)) Ric).toContinuousLinearMap
  let slots : Fin 4 -> Fin n := ![a, b, c, d]
  let rmSlots : Fin 4 -> Fin n := ![a, b, d, c]
  have hslots : (fun i => basis (slots i)) =
      vec4 (I := I) (basis a) (basis b) (basis c) (basis d) := by
    funext i
    fin_cases i <;> rfl
  have hrmSlots : (fun i => basis (rmSlots i)) =
      vec4 (I := I) (basis a) (basis b) (basis d) (basis c) := by
    funext i
    fin_cases i <;> rfl
  have hswapSlots : (fun q : Fin 4 => slots (curvatureSlotSwap q)) = rmSlots := by
    funext q
    fin_cases q <;> rfl
  have hRfun :
      (fun q : Fin 4 -> Fin n =>
        S.base.rm04 (t : Real) x (fun p => basis (q p))) =
        fun q => R (q 0) (q 1) (q 2) (q 3) := by
    funext q
    apply congrArg (S.base.rm04 (t : Real) x)
    funext p
    fin_cases p <;> rfl
  have hrough :
      metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n))
          ((Tensor0SField.domDomCongr ∞
            (frontExtendEquiv (frontExtendEquiv curvatureSlotSwap))
            (nablaKRm04Field (I := I) S (t : Real) 2)) x)
          (fun i => basis (slots i)) =
        tensor0SComponent (I := I)
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Fin n))
            (nablaKRm04Field (I := I) S (t : Real) 2 x))
          (fun i => basis i) rmSlots := by
    rw [metricTrace0S2TensorInBasis_apply]
    rw [tensor0SComponent_apply, metricTrace0S2TensorInBasis_apply]
    unfold metricTrace0S2InBasis
    simp only [Tensor0SField.domDomCongr_apply,
      Tensor0SSpace.domDomCongr_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    apply congrArg (nablaKRm04Field (I := I) S (t : Real) 2 x)
    funext q
    fin_cases q <;> rfl
  have haction :
      covariantEndomorphismAction0S (I := I)
          (hamiltonKField (I := I) S (t : Real) x) RicEnd
          (fun i => basis (slots i)) =
        (∑ p, RicComp a p * R p b d c) +
        (∑ p, RicComp b p * R a p d c) +
        (∑ p, RicComp c p * R a b d p) +
        (∑ p, RicComp d p * R a b p c) := by
    change tensor0SComponent (I := I)
        (covariantEndomorphismAction0S (I := I)
          (hamiltonKField (I := I) S (t : Real) x) RicEnd) basis slots = _
    rw [tensor0SComponent_covariantEndomorphismAction0S]
    unfold ricStarArray
    rw [Fin.sum_univ_four]
    simp only [RicEnd, LinearMap.coe_toContinuousLinearMap']
    simp_rw [ricciEnd_repr_orthonormal_matrix
      (I := I) (S.base.metric (t : Real)) basis horth Ric]
    simp only [hamiltonKField, Tensor0SField.domDomCongr_apply,
      Tensor0SSpace.domDomCongr_apply, tensor0SComponent_apply,
      Function.update_apply, slots, R, RicComp]
    congr 1
  rw [← hslots]
  rw [Tensor0SSpace.add_apply, Tensor0SSpace.sub_apply,
    hamiltonTensor0SOfComponents_apply, hrough, haction]
  rw [hswapSlots, hRfun]
  change _ = hamiltonRmReactionComponent R a b d c
  have hreaction := hamiltonRmReact_add_ricci_slot_actions_matrix
    R RicComp hRm hTrace a b d c
  change _ = hamiltonRmReactionComponent R a b d c at hreaction
  linear_combination hreaction

omit [SigmaCompactSpace M] in
private theorem hamiltonM_fixedHeat_component
    [I.Boundaryless]
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    let Mdot := hamiltonTensor0SOfComponents (I := I) basis
      (fun slots : Fin 2 → Fin n =>
        deriv (fun r : Real =>
          hamiltonMFamilyField (I := I) clock.origin r
            (S.base.metric r) x (fun i => basis (slots i))) clock.time)
    let derivs := CanonicalSpatialDerivs0S.ofSmoothConnection
      (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
      (hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time))
    let Ric := metricRicci (I := I) (M := M)
      (S.base.metric clock.time) x
    let RicEnd := (ricciEndAt (I := I)
      (S.base.metric clock.time) Ric).toContinuousLinearMap
    (Mdot - metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Fin n)) (derivs.nabla2A x) +
        covariantEndomorphismAction0S (I := I)
          (hamiltonMOriginField (I := I) clock.origin clock.time
            (S.base.metric clock.time) x) RicEnd)
        (vec2 (I := I) (basis a) (basis b)) =
      hamiltonMEvolutionReactionComponent clock
        (fun i j k l => S.base.rm04 clock.time x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => Ric (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric clock.time) x
          (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l => hamiltonNablaPField
          (I := I) (S.base.metric clock.time) x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => hamiltonDivPAt
          (I := I) (S.base.metric clock.time) x
          (vec2 (I := I) (basis i) (basis j))) a b := by
  classical
  dsimp only
  let g := S.base.metric clock.time
  let Mfield := hamiltonMOriginField (I := I) clock.origin clock.time g
  let Ric := metricRicci (I := I) (M := M) g x
  let RicEnd := (ricciEndAt (I := I) g Ric).toContinuousLinearMap
  let A := basis a
  let B := basis b
  let RA := RicEnd A
  let RB := RicEnd B
  let moving : Real → Real := fun r =>
    hamiltonMFamilyField (I := I) clock.origin r
      (S.base.metric r) x
      (vec2 (I := I) (A + (r - clock.time) • RA)
        (B + (r - clock.time) • RB))
  have hmove := hamiltonMAt_hasDerivWithinAt_of_ricci_flow
    (I := I) S hS clock ht x basis horth a b
  dsimp only at hmove
  have hmoveAt := hmove.hasDerivAt (D.regular_mem_nhds ht)
  have hfun : moving = fun r : Real =>
      hamiltonDivPAt (I := I) (S.base.metric r) x
          (vec2 (I := I)
            (oneTimeUhlenbeckVector (I := I) g clock.time r A)
            (oneTimeUhlenbeckVector (I := I) g clock.time r B)) +
        hamiltonCurvatureRicciAt (I := I) (S.base.metric r) x
          (vec2 (I := I)
            (oneTimeUhlenbeckVector (I := I) g clock.time r A)
            (oneTimeUhlenbeckVector (I := I) g clock.time r B)) +
        (1 / (2 * (r - clock.origin))) *
          metricRicci (I := I) (M := M) (S.base.metric r) x
            (vec2 (I := I)
              (oneTimeUhlenbeckVector (I := I) g clock.time r A)
              (oneTimeUhlenbeckVector (I := I) g clock.time r B)) := by
    funext r
    simp only [moving, hamiltonMFamilyField, hamiltonMOriginField_apply,
      Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul,
      LinearMap.coe_toContinuousLinearMap', A, B, RA, RB, RicEnd, Ric, g,
      oneTimeUhlenbeckVector]
  have hmoving : HasDerivAt moving (deriv moving clock.time) clock.time := by
    rw [hfun]
    exact hmoveAt.congr_deriv hmoveAt.deriv.symm
  have hmovingDeriv := hmoveAt.deriv
  rw [← hfun] at hmovingDeriv
  have hfixedWithin := tensor02At_hasDerivWithinAt_of_affine_slots
    (I := I) (s := Set.univ)
    (fun r : Real =>
      hamiltonMFamilyField (I := I) clock.origin r
        (S.base.metric r) x)
    A B RA RB (deriv moving clock.time)
    (fun X Y =>
      (hamiltonMFamilyField_eval_continuousAt
        (I := I) S hS clock ht x X Y).continuousWithinAt)
    hmoving.hasDerivWithinAt
  have hfixed := hfixedWithin.hasDerivAt Filter.univ_mem
  have hfixedDeriv := hfixed.deriv
  have hMdot :
      hamiltonTensor0SOfComponents (I := I) basis
          (fun slots : Fin 2 → Fin n =>
            deriv (fun r : Real =>
              hamiltonMFamilyField (I := I) clock.origin r
                (S.base.metric r) x (fun i => basis (slots i))) clock.time)
          (vec2 (I := I) A B) =
        deriv (fun r : Real =>
          hamiltonMFamilyField (I := I) clock.origin r
            (S.base.metric r) x (vec2 (I := I) A B)) clock.time := by
    let slots : Fin 2 → Fin n := ![a, b]
    have hslots : (fun i => basis (slots i)) = vec2 (I := I) A B := by
      funext i
      fin_cases i <;> rfl
    rw [show vec2 (I := I) A B = fun i => basis (slots i) from hslots.symm,
      hamiltonTensor0SOfComponents_apply]
  have hrough := hamiltonMOriginField_rough_laplacian_component
    (I := I) clock.origin clock.time g x basis horth a b
  dsimp only at hrough
  have haction :
      covariantEndomorphismAction0S (I := I) (Mfield x) RicEnd
          (vec2 (I := I) A B) =
        Mfield x (vec2 (I := I) RA B) +
          Mfield x (vec2 (I := I) A RB) := by
    rw [covariantEndomorphismAction0S_apply, Fin.sum_univ_two]
    congr 1
    · apply congrArg (Mfield x)
      funext i
      fin_cases i <;> simp [A, B, RA, vec2, Function.update]
    · apply congrArg (Mfield x)
      funext i
      fin_cases i <;> simp [A, B, RB, vec2, Function.update]
  change
    (hamiltonTensor0SOfComponents (I := I) basis _ - _ + _)
        (vec2 (I := I) A B) = _
  rw [Tensor0SSpace.add_apply, Tensor0SSpace.sub_apply, hMdot,
    hrough, haction, hfixedDeriv, hmovingDeriv]
  simp only [Mfield, g, Ric, A, B, RA, RB, RicEnd,
    hamiltonMFamilyField]
  have helapsed : clock.time - clock.origin ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt clock.origin_lt_time)
  rw [show clock.elapsed = clock.time - clock.origin by rfl]
  field_simp [helapsed]
  ring

omit [CompleteSpace E] [FiniteDimensional Real E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor0SSpace_product_finAddFlip_two
    {x : M} (A B : Tensor0SSpace 2 I x) :
    (A.product B).domDomCongr (finAddFlip (m := 2) (n := 2)) =
      B.product A := by
  ext v
  rw [Tensor0SSpace.domDomCongr_apply,
    Tensor0SSpace.product_apply, Tensor0SSpace.product_apply]
  have hleft0 :
      (fun i => v ((finAddFlip (m := 2) (n := 2)) i)) ∘ Fin.castAdd 2 =
        vec2 (I := I) (v 2) (v 3) := by
    funext i
    fin_cases i <;> rfl
  have hleft1 :
      (fun i => v ((finAddFlip (m := 2) (n := 2)) i)) ∘ Fin.natAdd 2 =
        vec2 (I := I) (v 0) (v 1) := by
    funext i
    fin_cases i <;> rfl
  have hright0 : v ∘ Fin.castAdd 2 = vec2 (I := I) (v 0) (v 1) := by
    funext i
    fin_cases i <;> rfl
  have hright1 : v ∘ Fin.natAdd 2 = vec2 (I := I) (v 2) (v 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hleft0, hleft1, hright0, hright1, mul_comm]

omit [CompleteSpace E] [FiniteDimensional Real E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor0SSpace_product_finAddFlip_one
    {x : M} (A B : Tensor0SSpace 1 I x) :
    (A.product B).domDomCongr (finAddFlip (m := 1) (n := 1)) =
      B.product A := by
  ext v
  rw [Tensor0SSpace.domDomCongr_apply,
    Tensor0SSpace.product_apply, Tensor0SSpace.product_apply]
  have hleft0 :
      (fun i => v ((finAddFlip (m := 1) (n := 1)) i)) ∘ Fin.castAdd 1 =
        (fun _ : Fin 1 => v 1) := by
    funext i
    fin_cases i
    rfl
  have hleft1 :
      (fun i => v ((finAddFlip (m := 1) (n := 1)) i)) ∘ Fin.natAdd 1 =
        (fun _ : Fin 1 => v 0) := by
    funext i
    fin_cases i
    rfl
  have hright0 : v ∘ Fin.castAdd 1 = (fun _ : Fin 1 => v 0) := by
    funext i
    fin_cases i
    rfl
  have hright1 : v ∘ Fin.natAdd 1 = (fun _ : Fin 1 => v 1) := by
    funext i
    fin_cases i
    rfl
  rw [hleft0, hleft1, hright0, hright1, mul_comm]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem inner0S_product_comm_two_of_finAddFlip
    {x : M} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)))
    (T : Tensor0SSpace 4 I x) (A B : Tensor0SSpace 2 I x)
    (hT : T.domDomCongr (finAddFlip (m := 2) (n := 2)) = T) :
    inner0S (I := I) g x 4 T (A.product B) =
      inner0S (I := I) g x 4 T (B.product A) := by
  have h := Tensor0SBundle.inner0S_domDomCongr
    (I := I) g x basis hinv (finAddFlip (m := 2) (n := 2))
      T (A.product B)
  rw [hT, tensor0SSpace_product_finAddFlip_two] at h
  exact h.symm

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem inner0S_product_comm_one_of_finAddFlip
    {x : M} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)))
    (T : Tensor0SSpace 2 I x) (A B : Tensor0SSpace 1 I x)
    (hT : T.domDomCongr (finAddFlip (m := 1) (n := 1)) = T) :
    inner0S (I := I) g x 2 T (A.product B) =
      inner0S (I := I) g x 2 T (B.product A) := by
  have h := Tensor0SBundle.inner0S_domDomCongr
    (I := I) g x basis hinv (finAddFlip (m := 1) (n := 1))
      T (A.product B)
  rw [hT, tensor0SSpace_product_finAddFlip_one] at h
  exact h.symm

omit [SigmaCompactSpace M] in
private theorem hamiltonKField_nabla_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes 4 (S.family.connection t)
      (hamiltonKField (I := I) S t)
      (Tensor0SField.domDomCongr ∞ (frontExtendEquiv curvatureSlotSwap)
        (nablaRm04Field (I := I) S t)) := by
  exact totalNabla0SRealizes_domDomCongr
    (I := I) (S.family.connection t) curvatureSlotSwap
      (S.base.rm04 t) (nablaRm04Field (I := I) S t)
      (nablaRm04Field_realizes (I := I) S t)

omit [SigmaCompactSpace M] in
private theorem hamiltonKField_nabla2_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes 5 (S.family.connection t)
      (Tensor0SField.domDomCongr ∞ (frontExtendEquiv curvatureSlotSwap)
        (nablaRm04Field (I := I) S t))
      (Tensor0SField.domDomCongr ∞
        (frontExtendEquiv (frontExtendEquiv curvatureSlotSwap))
        (nablaKRm04Field (I := I) S t 2)) := by
  have hbase : TotalNabla0SRealizes 5 (S.family.connection t)
      (nablaRm04Field (I := I) S t)
      (nablaKRm04Field (I := I) S t 2) := by
    simpa [nablaRm04Field, nablaKRm04Field] using
      (nablaKRm04Field_realizes (I := I) S t 1)
  exact totalNabla0SRealizes_domDomCongr
    (I := I) (S.family.connection t) (frontExtendEquiv curvatureSlotSwap)
      (nablaRm04Field (I := I) S t)
      (nablaKRm04Field (I := I) S t 2) hbase

omit [SigmaCompactSpace M] in
private theorem hamilton_bianchi_trace_at_orthonormal
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    SecondBianchiAt (I := I) (nablaRm04Field (I := I) S t x) ∧
      NablaRmSymmAt (I := I) (nablaRm04Field (I := I) S t x) ∧
        NablaRicTraceAt (I := I) basis
          (fun i j => if i = j then (1 : Real) else 0)
          (nablaRm04Field (I := I) S t x)
          (metricNablaRic (I := I) (M := M) (S.base.metric t) x) := by
  have hinv := metricInverseInBasis_of_orthonormal
    (I := I) (S.base.metric t) basis horth
  simpa [nablaRm04Field, SolutionOn.family, SolutionFamily.connection,
    SolutionFamily.rm04, metricNablaRic, metricCov, metricRm04, metricRicci,
    DifferentialGeometry.Geometry.Curvature.metricCov,
    DifferentialGeometry.Geometry.Curvature.metricRm04,
    DifferentialGeometry.Geometry.Curvature.metricRicci] using
    (DifferentialGeometry.Geometry.Connection.levi_civita_bianchi_trace_identities
      (I := I) (M := M) (S.base.metric t) basis
        (fun i j => if i = j then (1 : Real) else 0) hinv)

omit [SigmaCompactSpace M] in
private theorem hamilton_nabla_rm_components_pair_symm
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    ∀ e, Rm04PairSymm (fun a b c d =>
      nablaRm04Field (I := I) S t x
        (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d))) := by
  have hSymm := (hamilton_bianchi_trace_at_orthonormal
    (I := I) S t x basis horth).2.1
  intro e
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    simpa only [vec5] using
      hSymm.2.1 (basis e) (basis b) (basis a) (basis c) (basis d)
  · intro a b c d
    simpa only [vec5] using
      hSymm.1 (basis e) (basis a) (basis b) (basis c) (basis d)
  · intro a b c d
    simpa only [vec5] using
      hSymm.2.2 (basis e) (basis a) (basis b) (basis c) (basis d)

omit [SigmaCompactSpace M] in
private theorem hamilton_rm_components_symm
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Rm04Symm (fun a b c d => S.base.rm04 (t : Real) x
      (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))) := by
  have hRm13 := fun tau : RealTimeInterval.RegularTime D =>
    rm13OfSolution (I := I) S (tau : Real)
  have hLower := fun
      (tau : RealTimeInterval.RegularTime D) (y : M) =>
    solution_rm04LowersRm13At (I := I) S (tau : Real) y
  have hInput := rm04InputSkew_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hOutput := rm04OutputSkew_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hPair := rm04PairSymm_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hFirst := rm04FirstBianchi_regular
    (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j k l
    simpa only [vec4] using
      hInput (basis j) (basis i) (basis k) (basis l)
  · intro i j k l
    simpa only [vec4] using
      hOutput (basis i) (basis j) (basis k) (basis l)
  · intro i j k l
    simpa only [vec4] using
      hPair (basis i) (basis j) (basis k) (basis l)
  · intro i j k l
    simpa only [vec4] using
      hFirst (basis i) (basis j) (basis k) (basis l)

omit [SigmaCompactSpace M] in
private theorem hamilton_curvature_ricci_trace_components
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric (t : Real)).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    curvatureRicciTraceComponents
      (fun a b c d => S.base.rm04 (t : Real) x
        (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
      (fun a b => metricRicci (I := I) (M := M)
        (S.base.metric (t : Real)) x
          (vec2 (I := I) (basis a) (basis b))) := by
  intro i j
  symm
  simpa only [SolutionOn.ricci, SolutionFamily.ricci] using
    (ricci_diag_eq_sum_rm04_diag_of_orthonormal
      (I := I) (S.base.metric (t : Real)) basis
      (S.ricci (t : Real)) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real))
      (ricciTraceOfSolution (I := I) S (t : Real))
      (solution_rm04LowersRm13At (I := I) S (t : Real) x) horth i j)

omit [SigmaCompactSpace M] in
private theorem hamilton_contracted_curvature_derivative_components
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    contractedCurvatureDerivativeComponents
      (fun e a b c d => nablaRm04Field (I := I) S t x
        (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d)))
      (fun a b c => metricNablaRic (I := I) (M := M)
        (S.base.metric t) x
          (vec3 (I := I) (basis a) (basis b) (basis c))) := by
  intro p q r
  have hcore := hamilton_bianchi_trace_at_orthonormal
    (I := I) S t x basis horth
  have hDiv := curvature_divergence_eq_hamiltonP (I := I) basis
    (fun i j => if i = j then (1 : Real) else 0)
    (nablaRm04Field (I := I) S t x)
    (metricNablaRic (I := I) (M := M) (S.base.metric t) x)
    hcore.1 hcore.2.1 hcore.2.2 (basis r) (basis q) (basis p)
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, hamiltonP_apply] at hDiv
  rw [metricNablaRic_last_two_symm (I := I) (M := M)
      (S.base.metric t) x (basis q) (basis r) (basis p),
    metricNablaRic_last_two_symm (I := I) (M := M)
      (S.base.metric t) x (basis r) (basis q) (basis p)] at hDiv
  simpa only [vec3, vec5] using hDiv

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonBlock_scalar_row_sum
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {t : Real} {x : M}
    (qK qP qM : Real → M → Real)
    (aK aP aM : Real)
    (hKtime : HasDerivAt (fun r : Real => qK r x)
      (deriv (fun r : Real => qK r x) t) t)
    (hPtime : HasDerivAt (fun r : Real => qP r x)
      (deriv (fun r : Real => qP r x) t) t)
    (hMtime : HasDerivAt (fun r : Real => qM r x)
      (deriv (fun r : Real => qM r x) t) t)
    (hKSmooth : ContMDiff I 𝓘(Real, Real) ∞ (qK t))
    (hPSmooth : ContMDiff I 𝓘(Real, Real) ∞ (qP t))
    (hMSmooth : ContMDiff I 𝓘(Real, Real) ∞ (qM t))
    (hKheat : deriv (fun r : Real => qK r x) t -
      laplacianAt (I := I) G t (qK t) x = aK)
    (hPheat : deriv (fun r : Real => qP r x) t -
      laplacianAt (I := I) G t (qP t) x = aP)
    (hMheat : deriv (fun r : Real => qM r x) t -
      laplacianAt (I := I) G t (qM t) x = aM) :
    let q := fun r y => qK r y + 2 * qP r y + qM r y
    HasDerivAt (fun r : Real => q r x) (deriv (fun r : Real => q r x) t) t ∧
      deriv (fun r : Real => q r x) t -
          laplacianAt (I := I) G t (q t) x =
        aK + 2 * aP + aM := by
  dsimp only
  let q := fun r y => qK r y + 2 * qP r y + qM r y
  have htimeRaw := (hKtime.add (hPtime.const_mul 2)).add hMtime
  have htime' : HasDerivAt (fun r : Real => q r x)
      (deriv (fun r : Real => qK r x) t +
        2 * deriv (fun r : Real => qP r x) t +
          deriv (fun r : Real => qM r x) t) t := by
    have hfun :
        ((fun r : Real => qK r x) + fun r : Real => 2 * qP r x) +
            (fun r : Real => qM r x) =
          fun r : Real => q r x := by
      rfl
    rw [hfun] at htimeRaw
    exact htimeRaw
  have htime : HasDerivAt (fun r : Real => q r x)
      (deriv (fun r : Real => q r x) t) t :=
    htime'.congr_deriv htime'.deriv.symm
  refine ⟨htime, ?_⟩
  have hPScaledSmooth : ContMDiff I 𝓘(Real, Real) ∞
      (fun y : M => 2 * qP t y) := by
    exact (contMDiff_const : ContMDiff I _ ∞
      (fun _ : M => (2 : Real))).mul hPSmooth
  have hlapP := laplacianAt_smul (I := I) G t 2
    (hPSmooth.mdifferentiable (by simp))
    (gradientFun_mdiffAt (I := I) (G.metric t) hPSmooth x)
  have hlapKP := laplacianAt_add (I := I) G t
    (hKSmooth.mdifferentiable (by simp))
    (hPScaledSmooth.mdifferentiable (by simp))
    (gradientFun_mdiffAt (I := I) (G.metric t) hKSmooth x)
    (gradientFun_mdiffAt (I := I) (G.metric t) hPScaledSmooth x)
  have hKPSmooth : ContMDiff I 𝓘(Real, Real) ∞
      (fun y : M => qK t y + 2 * qP t y) :=
    hKSmooth.add hPScaledSmooth
  have hlapQ := laplacianAt_add (I := I) G t
    (hKPSmooth.mdifferentiable (by simp))
    (hMSmooth.mdifferentiable (by simp))
    (gradientFun_mdiffAt (I := I) (G.metric t) hKPSmooth x)
    (gradientFun_mdiffAt (I := I) (G.metric t) hMSmooth x)
  have hlap : laplacianAt (I := I) G t (q t) x =
      laplacianAt (I := I) G t (qK t) x +
        2 * laplacianAt (I := I) G t (qP t) x +
          laplacianAt (I := I) G t (qM t) x := by
    rw [show q t = fun y : M =>
      (qK t y + 2 * qP t y) + qM t y by rfl, hlapQ]
    rw [hlapKP]
    have hlapP' : laplacianAt (I := I) G t
        (fun y : M => 2 * qP t y) x =
          2 * laplacianAt (I := I) G t (qP t) x := by
      change laplacianAt (I := I) G t
          (fun y : M => 2 * qP t y) x = _ at hlapP
      exact hlapP
    rw [hlapP']
  rw [htime'.deriv, hlap]
  linear_combination hKheat + 2 * hPheat + hMheat

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem roughLap0STensor_eq_metricTrace0S2TensorInBasis_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : Nat}
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (T : Tensor0SSpace (s + 2) I x) :
    Geometry.Operator.roughLap0STensor (I := I) g T =
      metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Idx)) T := by
  ext tail
  rw [Geometry.Operator.roughLap0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Idx))
      (metricInverseInBasis_identity_of_orthonormal
        (I := I) g basis horth),
    metricTrace0S2TensorInBasis_apply]

omit [SigmaCompactSpace M] in
private theorem hamiltonKField_nabla_curry_finAddFlip
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (e : Fin n) :
    let nablaK := Tensor0SField.domDomCongr ∞
      (frontExtendEquiv curvatureSlotSwap) (nablaRm04Field (I := I) S t)
    (tensor0SCurry (I := I) (M := M) 4 x (nablaK x) (basis e)).domDomCongr
        (finAddFlip (m := 2) (n := 2)) =
      tensor0SCurry (I := I) (M := M) 4 x (nablaK x) (basis e) := by
  dsimp only
  have hSymm := (hamilton_bianchi_trace_at_orthonormal
    (I := I) S t x basis horth).2.1
  ext v
  rw [Tensor0SSpace.domDomCongr_apply, tensor0S_curry_apply_cons,
    Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0S_curry_apply_cons, Tensor0SSpace.domDomCongr_apply]
  have hleft :
      (fun i => (Fin.cons (basis e)
        (fun j => v ((finAddFlip (m := 2) (n := 2)) j)) :
          Fin 5 → TangentSpace I x)
          ((frontExtendEquiv curvatureSlotSwap) i)) =
        vec5 (I := I) (basis e) (v 2) (v 3) (v 1) (v 0) := by
    funext i
    fin_cases i <;> rfl
  have hright :
      (fun i => (Fin.cons (basis e) v : Fin 5 → TangentSpace I x)
        ((frontExtendEquiv curvatureSlotSwap) i)) =
        vec5 (I := I) (basis e) (v 0) (v 1) (v 3) (v 2) := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright]
  calc
    nablaRm04Field (I := I) S t x
        (vec5 (I := I) (basis e) (v 2) (v 3) (v 1) (v 0)) =
      nablaRm04Field (I := I) S t x
        (vec5 (I := I) (basis e) (v 1) (v 0) (v 2) (v 3)) :=
      hSymm.2.2 (basis e) (v 2) (v 3) (v 1) (v 0)
    _ = -nablaRm04Field (I := I) S t x
        (vec5 (I := I) (basis e) (v 0) (v 1) (v 2) (v 3)) :=
      hSymm.2.1 (basis e) (v 0) (v 1) (v 2) (v 3)
    _ = nablaRm04Field (I := I) S t x
        (vec5 (I := I) (basis e) (v 0) (v 1) (v 3) (v 2)) := by
      rw [hSymm.1 (basis e) (v 0) (v 1) (v 2) (v 3)]
      ring

omit [SigmaCompactSpace M] in
private theorem hamiltonMOriginField_finAddFlip
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M) :
    (hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time) x).domDomCongr
        (finAddFlip (m := 1) (n := 1)) =
      hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time) x := by
  ext v
  rw [Tensor0SSpace.domDomCongr_apply]
  have hM := hamiltonMAt_symm
    (I := I) S clock ht x (v 1) (v 0)
  have hfield := hamiltonMField_apply (I := I) S hS clock ht x
  change hamiltonMField (I := I) clock (S.base.metric clock.time) x
      (fun i => v ((finAddFlip (m := 1) (n := 1)) i)) =
    hamiltonMField (I := I) clock (S.base.metric clock.time) x v
  rw [hfield]
  have hleft :
      (fun i => v ((finAddFlip (m := 1) (n := 1)) i)) =
        vec2 (I := I) (v 1) (v 0) := by
    funext i
    fin_cases i <;> rfl
  have hright : v = vec2 (I := I) (v 0) (v 1) := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright]
  exact hM

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def inner0SSquareFixedHeatAt
    {Idx : Type*} [Fintype Idx]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (t : Real) (x : M) {s : Nat}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (fixedHeatT : Tensor0SSpace (s + s) I x)
    (nablaT : Tensor0SSpace (s + s + 1) I x)
    (T : Tensor0SSpace (s + s) I x)
    (nablaA : Tensor0SSpace (s + 1) I x)
    (A : Tensor0SSpace s I x) : Real :=
  inner0S (I := I) (G.metric t) x (s + s) fixedHeatT (A.product A) -
    4 * ∑ e : Idx,
      inner0S (I := I) (G.metric t) x (s + s)
        (tensor0SCurry (I := I) (M := M) (s + s) x nablaT (basis e))
        ((tensor0SCurry (I := I) (M := M) s x nablaA (basis e)).product A) -
    2 * ∑ e : Idx,
      inner0S (I := I) (G.metric t) x (s + s) T
        ((tensor0SCurry (I := I) (M := M) s x nablaA (basis e)).product
          (tensor0SCurry (I := I) (M := M) s x nablaA (basis e)))

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def inner0SProductFixedHeatAt
    {Idx : Type*} [Fintype Idx]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (t : Real) (x : M) {p q : Nat}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (fixedHeatT : Tensor0SSpace (p + q) I x)
    (T : Tensor0SSpace (p + q) I x)
    (nablaT : Tensor0SSpace (p + q + 1) I x)
    (fixedHeatA : Tensor0SSpace p I x)
    (A : Tensor0SSpace p I x) (nablaA : Tensor0SSpace (p + 1) I x)
    (fixedHeatB : Tensor0SSpace q I x)
    (B : Tensor0SSpace q I x) (nablaB : Tensor0SSpace (q + 1) I x) : Real :=
  inner0S (I := I) (G.metric t) x (p + q) fixedHeatT (A.product B) +
    inner0S (I := I) (G.metric t) x (p + q) T (fixedHeatA.product B) +
    inner0S (I := I) (G.metric t) x (p + q) T (A.product fixedHeatB) -
    2 * ∑ e : Idx,
      inner0S (I := I) (G.metric t) x (p + q)
        (tensor0SCurry (I := I) (M := M) (p + q) x nablaT (basis e))
        ((tensor0SCurry (I := I) (M := M) p x nablaA (basis e)).product B +
          A.product (tensor0SCurry (I := I) (M := M) q x nablaB (basis e))) -
    2 * ∑ e : Idx,
      inner0S (I := I) (G.metric t) x (p + q) T
        ((tensor0SCurry (I := I) (M := M) p x nablaA (basis e)).product
          (tensor0SCurry (I := I) (M := M) q x nablaB (basis e)))

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor0SFieldProduct_apply_eq_product
    {p q : Nat}
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q)
    (x : M) :
    tensor0SFieldProduct ∞ A B x = (A x).product (B x) := by
  ext v
  rw [tensor0SField_product_apply, Tensor0SSpace.product_apply]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem inner0S_product_contMDiff
    {p q : Nat}
    (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + q))
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q) :
    ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      inner0S (I := I) g y (p + q) (T y) ((A y).product (B y))) := by
  have heq :
      (fun y : M => inner0S (I := I) g y (p + q)
        (T y) ((A y).product (B y))) =
        fun y : M => inner0S (I := I) g y (p + q) (T y)
          (tensor0SFieldProduct ∞ A B y) := by
    funext y
    rw [tensor0SFieldProduct_apply_eq_product (I := I)]
  rw [heq]
  exact inner0S_contMDiff (I := I) g T (tensor0SFieldProduct ∞ A B)

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem inner0S_product_time_deriv_sub_laplacianAt_of_fixed_heats
    {p q : Nat} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {t : Real} {x : M}
    (Q : Tensor0SSpace 2 I x)
    (L : TangentSpace I x →L[Real] TangentSpace I x)
    (T : Real → Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + q))
    (nablaT : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + q + 1))
    (nabla2T : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + q + 2))
    (A : Real → Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ p)
    (nablaA : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + 1))
    (nabla2A : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (p + 2))
    (B : Real → Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ q)
    (nablaB : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (q + 1))
    (nabla2B : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (q + 2))
    (Tdot : Tensor0SSpace (p + q) I x)
    (Adot : Tensor0SSpace p I x) (Bdot : Tensor0SSpace q I x)
    (fixedHeatT : Tensor0SSpace (p + q) I x)
    (fixedHeatA : Tensor0SSpace p I x) (fixedHeatB : Tensor0SSpace q I x)
    (hQ : ∀ X Y : TangentSpace I x,
      Q (vec2 (I := I) X Y) = Q (vec2 (I := I) Y X))
    (hL : ∀ X Y : TangentSpace I x,
      (G.metric t).inner x (L X) Y = Q (vec2 (I := I) X Y))
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (G.metric r).inner x X Y)
        ((-2 : Real) * Q (vec2 (I := I) X Y)) t)
    (hTtime : ∀ v : Fin (p + q) → TangentSpace I x,
      HasDerivAt (fun r : Real => T r x v) (Tdot v) t)
    (hAtime : ∀ v : Fin p → TangentSpace I x,
      HasDerivAt (fun r : Real => A r x v) (Adot v) t)
    (hBtime : ∀ v : Fin q → TangentSpace I x,
      HasDerivAt (fun r : Real => B r x v) (Bdot v) t)
    (hTfirst : TotalNabla0SRealizes (p + q) (G.connection t) (T t) nablaT)
    (hTsecond : TotalNabla0SRealizes (p + q + 1)
      (G.connection t) nablaT nabla2T)
    (hAfirst : TotalNabla0SRealizes p (G.connection t) (A t) nablaA)
    (hAsecond : TotalNabla0SRealizes (p + 1)
      (G.connection t) nablaA nabla2A)
    (hBfirst : TotalNabla0SRealizes q (G.connection t) (B t) nablaB)
    (hBsecond : TotalNabla0SRealizes (q + 1)
      (G.connection t) nablaB nabla2B)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (G.connection t) (∞ : WithTop ℕ∞))
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j,
      (G.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (hTheat : Tdot - metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Idx)) (nabla2T x) +
      covariantEndomorphismAction0S (I := I) (T t x) L = fixedHeatT)
    (hAheat : Adot - metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Idx)) (nabla2A x) +
      covariantEndomorphismAction0S (I := I) (A t x) L = fixedHeatA)
    (hBheat : Bdot - metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Idx)) (nabla2B x) +
      covariantEndomorphismAction0S (I := I) (B t x) L = fixedHeatB) :
    ∃ d : Real,
      HasDerivAt (fun r : Real => inner0S (I := I) (G.metric r) x (p + q)
        (T r x) ((A r x).product (B r x))) d t ∧
      d - laplacianAt (I := I) G t (fun y =>
        inner0S (I := I) (G.metric t) y (p + q)
          (T t y) ((A t y).product (B t y))) x =
        inner0SProductFixedHeatAt (I := I) G t x basis fixedHeatT
          (T t x) (nablaT x) fixedHeatA (A t x) (nablaA x)
          fixedHeatB (B t x) (nablaB x) := by
  obtain ⟨htime, hevolution⟩ :=
    inner0S_product_time_deriv_sub_laplacianAt_eq_fixed_metric_orthonormal
      (I := I) (G := G) (t := t) (x := x)
      Q L T nablaT nabla2T A nablaA nabla2A B nablaB nabla2B
      Tdot Adot Bdot hQ hL hg hTtime hAtime hBtime hTfirst hTsecond
      hAfirst hAsecond hBfirst hBsecond hcov basis horth
  rw [hTheat, hAheat, hBheat] at hevolution
  refine ⟨_, htime, ?_⟩
  unfold inner0SProductFixedHeatAt
  exact hevolution

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem inner0S_square_time_deriv_sub_laplacianAt_of_fixed_heat_zero
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {t : Real} {x : M} {s : Nat}
    (Q : Tensor0SSpace 2 I x)
    (L : TangentSpace I x →L[Real] TangentSpace I x)
    (T : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (s + s))
    (nablaT : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (s + s + 1))
    (nabla2T : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (s + s + 2))
    (A : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s)
    (nablaA : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (s + 1))
    (nabla2A : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (s + 2))
    (Tdot : Tensor0SSpace (s + s) I x)
    (Adot : Tensor0SSpace s I x)
    (fixedHeatT : Tensor0SSpace (s + s) I x)
    (hQ : ∀ X Y : TangentSpace I x,
      Q (vec2 (I := I) X Y) = Q (vec2 (I := I) Y X))
    (hL : ∀ X Y : TangentSpace I x,
      (G.metric t).inner x (L X) Y = Q (vec2 (I := I) X Y))
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (G.metric r).inner x X Y)
        ((-2 : Real) * Q (vec2 (I := I) X Y)) t)
    (hTtime : ∀ v : Fin (s + s) → TangentSpace I x,
      HasDerivAt (fun r : Real => T r x v) (Tdot v) t)
    (hAtime : ∀ v : Fin s → TangentSpace I x,
      HasDerivAt (fun r : Real => A r x v) (Adot v) t)
    (hTfirst : TotalNabla0SRealizes (s + s) (G.connection t) (T t) nablaT)
    (hTsecond : TotalNabla0SRealizes (s + s + 1)
      (G.connection t) nablaT nabla2T)
    (hAfirst : TotalNabla0SRealizes s (G.connection t) (A t) nablaA)
    (hAsecond : TotalNabla0SRealizes (s + 1)
      (G.connection t) nablaA nabla2A)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (G.connection t) (∞ : WithTop ℕ∞))
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j,
      (G.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (hAheat : Adot - metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Idx)) (nabla2A x) +
      covariantEndomorphismAction0S (I := I) (A t x) L = 0)
    (hTheat : Tdot - metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Idx)) (nabla2T x) +
      covariantEndomorphismAction0S (I := I) (T t x) L = fixedHeatT)
    (hTflip : ∀ e : Idx,
      (tensor0SCurry (I := I) (M := M) (s + s) x (nablaT x) (basis e)).domDomCongr
          (finAddFlip (m := s) (n := s)) =
        tensor0SCurry (I := I) (M := M) (s + s) x (nablaT x) (basis e)) :
    ∃ d : Real,
      HasDerivAt (fun r : Real =>
        inner0S (I := I) (G.metric r) x (s + s)
          (T r x) ((A r x).product (A r x))) d t ∧
        d - laplacianAt (I := I) G t (fun y =>
          inner0S (I := I) (G.metric t) y (s + s)
            (T t y) ((A t y).product (A t y))) x =
          inner0SSquareFixedHeatAt (I := I) G t x basis fixedHeatT
            (nablaT x) (T t x) (nablaA x) (A t x) := by
  obtain ⟨htime, hevolution⟩ :=
    inner0S_product_time_deriv_sub_laplacianAt_eq_fixed_metric_orthonormal
      (I := I) (G := G) (t := t) (x := x)
      Q L T nablaT nabla2T A nablaA nabla2A A nablaA nabla2A
      Tdot Adot Adot hQ hL hg hTtime hAtime hAtime
      hTfirst hTsecond hAfirst hAsecond hAfirst hAsecond hcov basis horth
  rw [hAheat, hTheat] at hevolution
  have hzeroProductLeft :
      (0 : Tensor0SSpace s I x).product (A t x) = 0 := by
    ext v
    simp [Tensor0SSpace.product_apply]
  have hzeroProductRight :
      (A t x).product (0 : Tensor0SSpace s I x) = 0 := by
    ext v
    simp [Tensor0SSpace.product_apply]
  have hinnerZero (C : Tensor0SSpace (s + s) I x) :
      inner0S (I := I) (G.metric t) x (s + s) C 0 = 0 := by
    simp [inner0S, MetricFiberData.inner]
  rw [hzeroProductLeft, hzeroProductRight] at hevolution
  simp only [hinnerZero, add_zero] at hevolution
  have hinv := metricInverseInBasis_of_orthonormal
    (I := I) (G.metric t) basis horth
  have hcomm : ∀ e : Idx,
      inner0S (I := I) (G.metric t) x (s + s)
          (tensor0SCurry (I := I) (M := M) (s + s) x
            (nablaT x) (basis e))
          ((A t x).product
            (tensor0SCurry (I := I) (M := M) s x (nablaA x) (basis e))) =
        inner0S (I := I) (G.metric t) x (s + s)
          (tensor0SCurry (I := I) (M := M) (s + s) x
            (nablaT x) (basis e))
          ((tensor0SCurry (I := I) (M := M) s x
            (nablaA x) (basis e)).product (A t x)) := by
    intro e
    have h := Tensor0SBundle.inner0S_domDomCongr
      (I := I) (G.metric t) x basis hinv (finAddFlip (m := s) (n := s))
      (tensor0SCurry (I := I) (M := M) (s + s) x (nablaT x) (basis e))
      ((tensor0SCurry (I := I) (M := M) s x
        (nablaA x) (basis e)).product (A t x))
    rw [hTflip e] at h
    have hproduct :
        ((tensor0SCurry (I := I) (M := M) s x
            (nablaA x) (basis e)).product (A t x)).domDomCongr
            (finAddFlip (m := s) (n := s)) =
          (A t x).product
            (tensor0SCurry (I := I) (M := M) s x (nablaA x) (basis e)) := by
      ext v
      simp only [Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.product_apply]
      have hleft0 :
          (fun i => v ((finAddFlip (m := s) (n := s)) i)) ∘ Fin.castAdd s =
            v ∘ Fin.natAdd s := by
        funext i
        simp only [Function.comp_apply, finAddFlip_apply_castAdd]
      have hleft1 :
          (fun i => v ((finAddFlip (m := s) (n := s)) i)) ∘ Fin.natAdd s =
            v ∘ Fin.castAdd s := by
        funext i
        simp only [Function.comp_apply, finAddFlip_apply_natAdd]
      rw [hleft0, hleft1, mul_comm]
    rw [hproduct] at h
    exact h
  rw [inner0S_add_right] at htime
  simp_rw [inner0S_add_right, hcomm] at hevolution
  rw [Finset.sum_add_distrib] at hevolution
  refine ⟨_, htime, ?_⟩
  unfold inner0SSquareFixedHeatAt
  linear_combination hevolution

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem normSq0S_time_deriv_sub_laplacianAt_of_fixed_heat
    {s : Nat} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {t : Real} {x : M}
    (Q : Tensor0SSpace 2 I x)
    (L : TangentSpace I x →L[Real] TangentSpace I x)
    (A : Real → Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ s)
    (nablaA : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (s + 1))
    (nabla2A : Tensor0SField (E := E) (H := H)
      (I := I) (M := M) ∞ (s + 2))
    (Adot fixedHeat : Tensor0SSpace s I x)
    (hQ : ∀ X Y : TangentSpace I x,
      Q (fun a : Fin 2 => if a = 0 then X else Y) =
        Q (fun a : Fin 2 => if a = 0 then Y else X))
    (hL : ∀ X Y : TangentSpace I x,
      (G.metric t).inner x (L X) Y =
        Q (fun a : Fin 2 => if a = 0 then X else Y))
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (G.metric r).inner x X Y)
        ((-2 : Real) * Q (vec2 (I := I) X Y)) t)
    (hAt : ∀ v : Fin s → TangentSpace I x,
      HasDerivAt (fun r : Real => A r x v) (Adot v) t)
    (hA : TotalNabla0SRealizes s (G.connection t) (A t) nablaA)
    (h2A : TotalNabla0SRealizes (s + 1) (G.connection t) nablaA nabla2A)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (G.connection t) (∞ : WithTop ℕ∞))
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j,
      (G.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (hheat : Adot - metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Idx)) (nabla2A x) +
      covariantEndomorphismAction0S (I := I) (A t x) L = fixedHeat) :
    ∃ d : Real,
      HasDerivAt
        (fun r : Real => normSq0S (I := I) (G.metric r) x s (A r x)) d t ∧
      d - laplacianAt (I := I) G t
          (fun y : M => normSq0S (I := I) (G.metric t) y s (A t y)) x =
        2 * inner0S (I := I) (G.metric t) x s fixedHeat (A t x) -
          2 * ∑ e : Idx,
            inner0S (I := I) (G.metric t) x s
              (tensor0SCurry (I := I) (M := M) s x (nablaA x) (basis e))
              (tensor0SCurry (I := I) (M := M) s x (nablaA x) (basis e)) := by
  obtain ⟨htime, hevolution⟩ :=
    inner0S_time_deriv_sub_laplacianAt_eq_fixed_metric_orthonormal
      (I := I) (G := G) (t := t) (x := x) Q L A nablaA nabla2A
        A nablaA nabla2A Adot Adot hQ hL hg hAt hAt hA h2A hA h2A
        hcov basis horth
  rw [hheat] at hevolution
  have hsymm : inner0S (I := I) (G.metric t) x s (A t x) fixedHeat =
      inner0S (I := I) (G.metric t) x s fixedHeat (A t x) :=
    inner0S_symm (I := I) (G.metric t) x (A t x) fixedHeat
  let d := ricciReaction0S (I := I) (G.metric t) x s Q (A t x) (A t x) +
    inner0S (I := I) (G.metric t) x s Adot (A t x) +
      inner0S (I := I) (G.metric t) x s (A t x) Adot
  refine ⟨d, ?_, ?_⟩
  · simpa only [normSq0S_eq_inner, d] using htime
  · simp only [normSq0S_eq_inner, d]
    rw [hevolution, hsymm]
    ring

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonKTestScalar
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (U : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (r : Real) (y : M) : Real :=
  inner0S (I := I) ((flowG (I := I) S).metric r) y 4
    (hamiltonKField (I := I) S r y) ((U r y).product (U r y))

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonKTimeDerivativeAt
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Tensor0SSpace 4 I x :=
  hamiltonTensor0SOfComponents (I := I) basis
    (fun slots : Fin 4 → Fin n =>
      let rmSlots := fun q : Fin 4 => slots (curvatureSlotSwap q)
      tensor0SComponent (I := I)
          (metricTrace0S2TensorInBasis (I := I) basis
            (identityInvMetric (Idx := Fin n))
            (nablaKRm04Field (I := I) S t 2 x))
          (fun i => basis i) rmSlots +
        DifferentialGeometry.Geometry.Connection.hamiltonRmReact
          (fun q : Fin 4 → Fin n =>
            S.base.rm04 t x (fun p => basis (q p))) rmSlots)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonKNablaField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 5 :=
  Tensor0SField.domDomCongr ∞ (frontExtendEquiv curvatureSlotSwap)
    (nablaRm04Field (I := I) S t)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonKNabla2Field
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 6 :=
  Tensor0SField.domDomCongr ∞
    (frontExtendEquiv (frontExtendEquiv curvatureSlotSwap))
    (nablaKRm04Field (I := I) S t 2)

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonTestUNablaField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (U : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  (CanonicalSpatialDerivs0S.ofSmoothConnection
    (I := I) (metricCov (I := I) (M := M) (S.base.metric t))
    (metricCov_smooth (I := I) (M := M) (S.base.metric t)) (U t)).nablaA

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonTestUNabla2Field
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (U : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  (CanonicalSpatialDerivs0S.ofSmoothConnection
    (I := I) (metricCov (I := I) (M := M) (S.base.metric t))
    (metricCov_smooth (I := I) (M := M) (S.base.metric t)) (U t)).nabla2A

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonTestRicciAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M) : Tensor0SSpace 2 I x :=
  metricRicci (I := I) (M := M) (S.base.metric clock.time) x

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonTestRicciEndAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x :=
  (ricciEndAt (I := I) (S.base.metric clock.time)
    (hamiltonTestRicciAt (I := I) S clock x)).toContinuousLinearMap

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonKFixedHeatAt
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Tensor0SSpace 4 I x :=
  hamiltonKTimeDerivativeAt (I := I) S clock.time x basis -
      metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Fin n))
        (hamiltonKNabla2Field (I := I) S clock.time x) +
    covariantEndomorphismAction0S (I := I)
      (hamiltonKField (I := I) S clock.time x)
      (hamiltonTestRicciEndAt (I := I) S clock x)

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonKTestScalarHeatAt
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (U : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2) : Real :=
  inner0SSquareFixedHeatAt (I := I) (flowG (I := I) S) clock.time x basis
    (hamiltonKFixedHeatAt (I := I) S clock x basis)
    (hamiltonKNablaField (I := I) S clock.time x)
    (hamiltonKField (I := I) S clock.time x)
    (hamiltonTestUNablaField (I := I) S clock.time U x) (U clock.time x)

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonTestUTimeAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (U : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2) :
    Tensor0SSpace 2 I x :=
  let g := S.base.metric clock.time
  Geometry.Operator.roughLap0STensor (I := I) g
      (hamiltonTestUNabla2Field (I := I) S clock.time U x) -
    covariantEndomorphismAction0S (I := I) (U clock.time x)
      (ricciEndAt (I := I) g
        (metricRicci (I := I) (M := M) g x)).toContinuousLinearMap

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonPTimeDerivativeAt
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Tensor0SSpace 3 I x :=
  hamiltonTensor0SOfComponents (I := I) basis
    (fun slots : Fin 3 → Fin n =>
      deriv (fun r : Real => hamiltonPField (I := I) (S.base.metric r) x
        (fun i => basis (slots i))) t)

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonPNablaField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  (CanonicalSpatialDerivs0S.ofSmoothConnection
    (I := I) (metricCov (I := I) (M := M) (S.base.metric t))
    (metricCov_smooth (I := I) (M := M) (S.base.metric t))
    (hamiltonPField (I := I) (S.base.metric t))).nablaA

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonPNabla2Field
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 5 :=
  (CanonicalSpatialDerivs0S.ofSmoothConnection
    (I := I) (metricCov (I := I) (M := M) (S.base.metric t))
    (metricCov_smooth (I := I) (M := M) (S.base.metric t))
    (hamiltonPField (I := I) (S.base.metric t))).nabla2A

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonMTimeDerivativeAt
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Tensor0SSpace 2 I x :=
  hamiltonTensor0SOfComponents (I := I) basis
    (fun slots : Fin 2 → Fin n =>
      deriv (fun r : Real => hamiltonMFamilyField (I := I) clock.origin r
        (S.base.metric r) x (fun i => basis (slots i))) clock.time)

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonMNablaField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  (CanonicalSpatialDerivs0S.ofSmoothConnection
    (I := I) (metricCov (I := I) (M := M) (S.base.metric clock.time))
    (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
    (hamiltonMOriginField (I := I) clock.origin clock.time
      (S.base.metric clock.time))).nablaA

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonMNabla2Field
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  (CanonicalSpatialDerivs0S.ofSmoothConnection
    (I := I) (metricCov (I := I) (M := M) (S.base.metric clock.time))
    (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
    (hamiltonMOriginField (I := I) clock.origin clock.time
      (S.base.metric clock.time))).nabla2A

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonTestWNablaField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock)
    (W : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  (CanonicalSpatialDerivs0S.ofSmoothConnection
    (I := I) (metricCov (I := I) (M := M) (S.base.metric clock.time))
    (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
    (W clock.time)).nablaA

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonTestWNabla2Field
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock)
    (W : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  (CanonicalSpatialDerivs0S.ofSmoothConnection
    (I := I) (metricCov (I := I) (M := M) (S.base.metric clock.time))
    (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
    (W clock.time)).nabla2A

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonTestWTimeAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock) (x : M)
    (W : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1) :
    Tensor0SSpace 1 I x :=
  Geometry.Operator.roughLap0STensor (I := I) (S.base.metric clock.time)
      (hamiltonTestWNabla2Field (I := I) S clock W x) +
    (1 / clock.elapsed : Real) • W clock.time x -
    covariantEndomorphismAction0S (I := I) (W clock.time x)
      (hamiltonTestRicciEndAt (I := I) S clock x)

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonPFixedHeatAt
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Tensor0SSpace 3 I x :=
  hamiltonPTimeDerivativeAt (I := I) S clock.time x basis -
      metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Fin n))
        (hamiltonPNabla2Field (I := I) S clock.time x) +
    covariantEndomorphismAction0S (I := I)
      (hamiltonPField (I := I) (S.base.metric clock.time) x)
      (hamiltonTestRicciEndAt (I := I) S clock x)

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonMFixedHeatAt
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    Tensor0SSpace 2 I x :=
  hamiltonMTimeDerivativeAt (I := I) S clock x basis -
      metricTrace0S2TensorInBasis (I := I) basis
        (identityInvMetric (Idx := Fin n))
        (hamiltonMNabla2Field (I := I) S clock x) +
    covariantEndomorphismAction0S (I := I)
      (hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time) x)
      (hamiltonTestRicciEndAt (I := I) S clock x)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonPTestScalar
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (U : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (W : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (r : Real) (y : M) : Real :=
  inner0S (I := I) ((flowG (I := I) S).metric r) y 3
    (hamiltonPField (I := I) (S.base.metric r) y)
    ((U r y).product (W r y))

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonPTestScalarHeatAt
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (U : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (W : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1) : Real :=
  inner0SProductFixedHeatAt (I := I) (flowG (I := I) S) clock.time x basis
    (hamiltonPFixedHeatAt (I := I) S clock x basis)
    (hamiltonPField (I := I) (S.base.metric clock.time) x)
    (hamiltonPNablaField (I := I) S clock.time x) 0
    (U clock.time x) (hamiltonTestUNablaField (I := I) S clock.time U x)
    ((1 / clock.elapsed : Real) • W clock.time x)
    (W clock.time x) (hamiltonTestWNablaField (I := I) S clock W x)

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonMTestScalar
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock)
    (W : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (r : Real) (y : M) : Real :=
  inner0S (I := I) ((flowG (I := I) S).metric r) y 2
    (hamiltonMFamilyField (I := I) clock.origin r (S.base.metric r) y)
    ((W r y).product (W r y))

omit [CompleteSpace E] [SigmaCompactSpace M] in
private noncomputable def hamiltonMTestScalarHeatAt
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (W : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1) : Real :=
  inner0SProductFixedHeatAt (I := I) (flowG (I := I) S) clock.time x basis
    (hamiltonMFixedHeatAt (I := I) S clock x basis)
    (hamiltonMOriginField (I := I) clock.origin clock.time
      (S.base.metric clock.time) x)
    (hamiltonMNablaField (I := I) S clock x)
    ((1 / clock.elapsed : Real) • W clock.time x)
    (W clock.time x) (hamiltonTestWNablaField (I := I) S clock W x)
    ((1 / clock.elapsed : Real) • W clock.time x)
    (W clock.time x) (hamiltonTestWNablaField (I := I) S clock W x)

omit [SigmaCompactSpace M] in
private theorem hamiltonKTimeDerivativeAt_realizes
    [I.Boundaryless]
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    ∀ v : Fin 4 → TangentSpace I x,
      HasDerivAt (fun r : Real => hamiltonKField (I := I) S r x v)
        (hamiltonKTimeDerivativeAt (I := I) S clock.time x basis v) clock.time := by
  simpa only [hamiltonKTimeDerivativeAt] using
    (hamiltonKField_hasDerivAt (I := I) S hS
      ⟨clock.time, ht⟩ x basis horth)

omit [SigmaCompactSpace M] in
private theorem hamiltonPTimeDerivativeAt_realizes
    [I.Boundaryless]
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    ∀ v : Fin 3 → TangentSpace I x,
      HasDerivAt
        (fun r : Real => hamiltonPField (I := I) (S.base.metric r) x v)
        (hamiltonPTimeDerivativeAt (I := I) S clock.time x basis v) clock.time := by
  simpa only [hamiltonPTimeDerivativeAt] using
    (hamiltonPField_hasDerivAt (I := I) S hS ⟨clock.time, ht⟩ x basis)

omit [SigmaCompactSpace M] in
private theorem hamiltonMTimeDerivativeAt_realizes
    [I.Boundaryless]
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r : Real => hamiltonMFamilyField (I := I) clock.origin r
        (S.base.metric r) x v)
        (hamiltonMTimeDerivativeAt (I := I) S clock x basis v) clock.time := by
  simpa only [hamiltonMTimeDerivativeAt] using
    (hamiltonMFamilyField_hasDerivAt (I := I) S hS clock ht x basis horth)

omit [SigmaCompactSpace M] in
private theorem hamiltonKNablaField_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes 4 ((flowG (I := I) S).connection t)
      (hamiltonKField (I := I) S t)
      (hamiltonKNablaField (I := I) S t) := by
  simpa [flowG, SolutionFamily.connection, metricCov, hamiltonKNablaField] using
    (hamiltonKField_nabla_realizes (I := I) S t)

omit [SigmaCompactSpace M] in
private theorem hamiltonKNabla2Field_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes 5 ((flowG (I := I) S).connection t)
      (hamiltonKNablaField (I := I) S t)
      (hamiltonKNabla2Field (I := I) S t) := by
  simpa [flowG, SolutionFamily.connection, metricCov, hamiltonKNablaField,
    hamiltonKNabla2Field] using
    (hamiltonKField_nabla2_realizes (I := I) S t)

omit [SigmaCompactSpace M] in
private theorem hamiltonKNablaField_curry_finAddFlip
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) (e : Fin n) :
    (tensor0SCurry (I := I) (M := M) 4 x
      (hamiltonKNablaField (I := I) S t x) (basis e)).domDomCongr
        (finAddFlip (m := 2) (n := 2)) =
      tensor0SCurry (I := I) (M := M) 4 x
        (hamiltonKNablaField (I := I) S t x) (basis e) := by
  simpa only [hamiltonKNablaField] using
    (hamiltonKField_nabla_curry_finAddFlip
      (I := I) S t x basis horth e)

omit [SigmaCompactSpace M] in
private theorem hamiltonTestUNablaField_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (U : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2) :
    TotalNabla0SRealizes 2 ((flowG (I := I) S).connection t) (U t)
      (hamiltonTestUNablaField (I := I) S t U) := by
  simpa [flowG, SolutionFamily.connection, metricCov, hamiltonTestUNablaField] using
    (CanonicalSpatialDerivs0S.ofSmoothConnection
      (I := I) (metricCov (I := I) (M := M) (S.base.metric t))
      (metricCov_smooth (I := I) (M := M) (S.base.metric t)) (U t)).first

omit [SigmaCompactSpace M] in
private theorem hamiltonTestUNabla2Field_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (U : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2) :
    TotalNabla0SRealizes 3 ((flowG (I := I) S).connection t)
      (hamiltonTestUNablaField (I := I) S t U)
      (hamiltonTestUNabla2Field (I := I) S t U) := by
  simpa [flowG, SolutionFamily.connection, metricCov, hamiltonTestUNablaField,
    hamiltonTestUNabla2Field] using
    (CanonicalSpatialDerivs0S.ofSmoothConnection
      (I := I) (metricCov (I := I) (M := M) (S.base.metric t))
      (metricCov_smooth (I := I) (M := M) (S.base.metric t)) (U t)).second

omit [SigmaCompactSpace M] in
private theorem hamiltonPNablaField_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes 3 ((flowG (I := I) S).connection t)
      (hamiltonPField (I := I) (S.base.metric t))
      (hamiltonPNablaField (I := I) S t) := by
  simpa [flowG, SolutionFamily.connection, metricCov, hamiltonPNablaField] using
    (CanonicalSpatialDerivs0S.ofSmoothConnection
      (I := I) (metricCov (I := I) (M := M) (S.base.metric t))
      (metricCov_smooth (I := I) (M := M) (S.base.metric t))
      (hamiltonPField (I := I) (S.base.metric t))).first

omit [SigmaCompactSpace M] in
private theorem hamiltonPNabla2Field_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes 4 ((flowG (I := I) S).connection t)
      (hamiltonPNablaField (I := I) S t)
      (hamiltonPNabla2Field (I := I) S t) := by
  simpa [flowG, SolutionFamily.connection, metricCov, hamiltonPNablaField,
    hamiltonPNabla2Field] using
    (CanonicalSpatialDerivs0S.ofSmoothConnection
      (I := I) (metricCov (I := I) (M := M) (S.base.metric t))
      (metricCov_smooth (I := I) (M := M) (S.base.metric t))
      (hamiltonPField (I := I) (S.base.metric t))).second

omit [SigmaCompactSpace M] in
private theorem hamiltonMNablaField_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock) :
    TotalNabla0SRealizes 2 ((flowG (I := I) S).connection clock.time)
      (hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time)) (hamiltonMNablaField (I := I) S clock) := by
  simpa [flowG, SolutionFamily.connection, metricCov, hamiltonMNablaField] using
    (CanonicalSpatialDerivs0S.ofSmoothConnection
      (I := I) (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
      (hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time))).first

omit [SigmaCompactSpace M] in
private theorem hamiltonMNabla2Field_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock) :
    TotalNabla0SRealizes 3 ((flowG (I := I) S).connection clock.time)
      (hamiltonMNablaField (I := I) S clock)
      (hamiltonMNabla2Field (I := I) S clock) := by
  simpa [flowG, SolutionFamily.connection, metricCov, hamiltonMNablaField,
    hamiltonMNabla2Field] using
    (CanonicalSpatialDerivs0S.ofSmoothConnection
      (I := I) (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
      (hamiltonMOriginField (I := I) clock.origin clock.time
        (S.base.metric clock.time))).second

omit [SigmaCompactSpace M] in
private theorem hamiltonTestWNablaField_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock)
    (W : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1) :
    TotalNabla0SRealizes 1 ((flowG (I := I) S).connection clock.time)
      (W clock.time) (hamiltonTestWNablaField (I := I) S clock W) := by
  simpa [flowG, SolutionFamily.connection, metricCov, hamiltonTestWNablaField] using
    (CanonicalSpatialDerivs0S.ofSmoothConnection
      (I := I) (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
      (W clock.time)).first

omit [SigmaCompactSpace M] in
private theorem hamiltonTestWNabla2Field_realizes
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (clock : HarnackClock)
    (W : Real → Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1) :
    TotalNabla0SRealizes 2 ((flowG (I := I) S).connection clock.time)
      (hamiltonTestWNablaField (I := I) S clock W)
      (hamiltonTestWNabla2Field (I := I) S clock W) := by
  simpa [flowG, SolutionFamily.connection, metricCov, hamiltonTestWNablaField,
    hamiltonTestWNabla2Field] using
    (CanonicalSpatialDerivs0S.ofSmoothConnection
      (I := I) (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
      (W clock.time)).second

omit [SigmaCompactSpace M] in
private theorem hamiltonTestU_fixed_heat_zero
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (U : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2) :
    hamiltonTestUTimeAt (I := I) S clock x U -
        metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n))
          (hamiltonTestUNabla2Field (I := I) S clock.time U x) +
      covariantEndomorphismAction0S (I := I) (U clock.time x)
        (ricciEndAt (I := I) (S.base.metric clock.time)
          (metricRicci (I := I) (M := M)
            (S.base.metric clock.time) x)).toContinuousLinearMap = 0 := by
  rw [← roughLap0STensor_eq_metricTrace0S2TensorInBasis_orthonormal
    (I := I) (S.base.metric clock.time) basis horth
      (hamiltonTestUNabla2Field (I := I) S clock.time U x)]
  simp only [hamiltonTestUTimeAt]
  abel

omit [SigmaCompactSpace M] in
private theorem hamiltonTestW_fixed_heat
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (W : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1) :
    hamiltonTestWTimeAt (I := I) S clock x W -
        metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n))
          (hamiltonTestWNabla2Field (I := I) S clock W x) +
      covariantEndomorphismAction0S (I := I) (W clock.time x)
        (hamiltonTestRicciEndAt (I := I) S clock x) =
      (1 / clock.elapsed : Real) • W clock.time x := by
  rw [← roughLap0STensor_eq_metricTrace0S2TensorInBasis_orthonormal
    (I := I) (S.base.metric clock.time) basis horth
      (hamiltonTestWNabla2Field (I := I) S clock W x)]
  simp only [hamiltonTestWTimeAt]
  abel

omit [SigmaCompactSpace M] in
private theorem hamiltonPFixedHeatAt_component
    [I.Boundaryless]
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b c : Fin n) :
    hamiltonPFixedHeatAt (I := I) S clock x basis
        (vec3 (I := I) (basis a) (basis b) (basis c)) =
      hamiltonPEvolutionReactionComponent
        (fun i j k l => S.base.rm04 clock.time x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric clock.time) x
            (vec2 (I := I) (basis i) (basis j)))
        (fun i j k l m => nablaRm04Field (I := I) S clock.time x
          (vec5 (I := I) (basis i) (basis j) (basis k) (basis l)
            (basis m)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric clock.time) x
            (vec3 (I := I) (basis i) (basis j) (basis k))) a b c := by
  let slots : Fin 3 → Fin n := ![a, b, c]
  have hslots : (fun i => basis (slots i)) =
      vec3 (I := I) (basis a) (basis b) (basis c) := by
    funext i
    fin_cases i <;> rfl
  have htime :
      hamiltonPTimeDerivativeAt (I := I) S clock.time x basis
          (vec3 (I := I) (basis a) (basis b) (basis c)) =
        deriv (fun r : Real => hamiltonPField (I := I)
          (S.base.metric r) x
            (vec3 (I := I) (basis a) (basis b) (basis c))) clock.time := by
    rw [show vec3 (I := I) (basis a) (basis b) (basis c) =
      fun i => basis (slots i) from hslots.symm,
      hamiltonPTimeDerivativeAt, hamiltonTensor0SOfComponents_apply]
  rw [hamiltonPFixedHeatAt, Tensor0SSpace.add_apply,
    Tensor0SSpace.sub_apply, htime]
  simpa only [hamiltonPNabla2Field, hamiltonTestRicciEndAt,
    hamiltonTestRicciAt] using
    (hamiltonP_fixed_heat_component_of_ricci_flow
      (I := I) S hS ⟨clock.time, ht⟩ x basis horth a b c)

omit [SigmaCompactSpace M] in
private theorem hamiltonMFixedHeatAt_component
    [I.Boundaryless]
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (a b : Fin n) :
    hamiltonMFixedHeatAt (I := I) S clock x basis
        (vec2 (I := I) (basis a) (basis b)) =
      hamiltonMEvolutionReactionComponent clock
        (fun i j k l => S.base.rm04 clock.time x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => metricRicci (I := I) (M := M)
          (S.base.metric clock.time) x
            (vec2 (I := I) (basis i) (basis j)))
        (fun i j k => metricNablaRic (I := I) (M := M)
          (S.base.metric clock.time) x
            (vec3 (I := I) (basis i) (basis j) (basis k)))
        (fun i j k l => hamiltonNablaPField
          (I := I) (S.base.metric clock.time) x
            (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
        (fun i j => hamiltonDivPAt
          (I := I) (S.base.metric clock.time) x
            (vec2 (I := I) (basis i) (basis j))) a b := by
  simpa only [hamiltonMFixedHeatAt, hamiltonMTimeDerivativeAt,
    hamiltonMNabla2Field, hamiltonTestRicciEndAt, hamiltonTestRicciAt] using
    (hamiltonM_fixedHeat_component
      (I := I) S hS clock ht x basis horth a b)

omit [SigmaCompactSpace M] in
private theorem hamiltonTestRicciAt_symm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M) :
    ∀ X Y : TangentSpace I x,
      hamiltonTestRicciAt (I := I) S clock x (vec2 (I := I) X Y) =
        hamiltonTestRicciAt (I := I) S clock x (vec2 (I := I) Y X) := by
  intro X Y
  exact metricRicciAt_symm (I := I) (S.base.metric clock.time) x X Y

omit [SigmaCompactSpace M] in
private theorem hamiltonTestRicciEndAt_inner
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M) :
    ∀ X Y : TangentSpace I x,
      (S.base.metric clock.time).inner x
          (hamiltonTestRicciEndAt (I := I) S clock x X) Y =
        hamiltonTestRicciAt (I := I) S clock x (vec2 (I := I) X Y) := by
  intro X Y
  exact ricciEnd_inner (I := I) (S.base.metric clock.time)
    (hamiltonTestRicciAt (I := I) S clock x) X Y

omit [SigmaCompactSpace M] in
private theorem flowMetric_inner_hasDerivAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M) :
    ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (S.base.metric r).inner x X Y)
        ((-2 : Real) *
          hamiltonTestRicciAt (I := I) S clock x (vec2 (I := I) X Y))
        clock.time := by
  intro X Y
  have hwithin := hS.equation ⟨clock.time, ht⟩ x X Y
  have hat := hwithin.hasDerivAt (D.regular_mem_nhds ht)
  simpa [hamiltonTestRicciAt, SolutionOn.ricci, SolutionOn.ricciAt,
    SolutionFamily.ricci, SolutionFamily.ricciAt, metricRicci,
    metricRicciAt] using hat

omit [SigmaCompactSpace M] [T2Space M] in
private theorem flowG_connection_smooth
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      ((flowG (I := I) S).connection t) (∞ : WithTop ℕ∞) := by
  simpa [flowG, SolutionFamily.connection, metricCov] using
    metricCov_smooth (I := I) (M := M) (S.base.metric t)

omit [SigmaCompactSpace M] in
private theorem hamiltonTestU_normSq_evolution
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (U : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (hUtime : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r : Real => U r x v)
        (hamiltonTestUTimeAt (I := I) S clock x U v) clock.time) :
    ∃ d : Real,
      HasDerivAt (fun r : Real =>
        normSq0S (I := I) ((flowG (I := I) S).metric r) x 2 (U r x)) d
          clock.time ∧
      d - laplacianAt (I := I) (flowG (I := I) S) clock.time
          (fun y : M => normSq0S (I := I)
            ((flowG (I := I) S).metric clock.time) y 2 (U clock.time y)) x =
        -2 * ∑ e : Fin n,
          inner0S (I := I) ((flowG (I := I) S).metric clock.time) x 2
            (tensor0SCurry (I := I) (M := M) 2 x
              (hamiltonTestUNablaField (I := I) S clock.time U x) (basis e))
            (tensor0SCurry (I := I) (M := M) 2 x
              (hamiltonTestUNablaField (I := I) S clock.time U x)
                (basis e)) := by
  obtain ⟨d, htime, hevolution⟩ :=
    normSq0S_time_deriv_sub_laplacianAt_of_fixed_heat
      (I := I) (G := flowG (I := I) S) (t := clock.time) (x := x)
      (hamiltonTestRicciAt (I := I) S clock x)
      (hamiltonTestRicciEndAt (I := I) S clock x) U
      (hamiltonTestUNablaField (I := I) S clock.time U)
      (hamiltonTestUNabla2Field (I := I) S clock.time U)
      (hamiltonTestUTimeAt (I := I) S clock x U) 0
      (hamiltonTestRicciAt_symm (I := I) S clock x)
      (hamiltonTestRicciEndAt_inner (I := I) S clock x)
      (flowMetric_inner_hasDerivAt (I := I) S hS clock ht x) hUtime
      (hamiltonTestUNablaField_realizes (I := I) S clock.time U)
      (hamiltonTestUNabla2Field_realizes (I := I) S clock.time U)
      (flowG_connection_smooth (I := I) S clock.time) basis horth
      (hamiltonTestU_fixed_heat_zero (I := I) S clock x basis horth U)
  have hinnerZero : inner0S (I := I)
      ((flowG (I := I) S).metric clock.time) x 2
      0 (U clock.time x) = 0 := by
    simp [inner0S, MetricFiberData.inner]
  refine ⟨d, htime, ?_⟩
  rw [hevolution, hinnerZero]
  ring

omit [SigmaCompactSpace M] in
private theorem hamiltonTestW_normSq_evolution
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (W : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (hWtime : ∀ v : Fin 1 → TangentSpace I x,
      HasDerivAt (fun r : Real => W r x v)
        (hamiltonTestWTimeAt (I := I) S clock x W v) clock.time)
    (hDW : totalNabla0SFun (I := I) (M := M) 1
      (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (W clock.time) x = 0) :
    ∃ d : Real,
      HasDerivAt (fun r : Real =>
        normSq0S (I := I) ((flowG (I := I) S).metric r) x 1 (W r x)) d
          clock.time ∧
      d - laplacianAt (I := I) (flowG (I := I) S) clock.time
          (fun y : M => normSq0S (I := I)
            ((flowG (I := I) S).metric clock.time) y 1 (W clock.time y)) x =
        (2 / clock.elapsed) *
          normSq0S (I := I) ((flowG (I := I) S).metric clock.time) x 1
            (W clock.time x) := by
  obtain ⟨d, htime, hevolution⟩ :=
    normSq0S_time_deriv_sub_laplacianAt_of_fixed_heat
      (I := I) (G := flowG (I := I) S) (t := clock.time) (x := x)
      (hamiltonTestRicciAt (I := I) S clock x)
      (hamiltonTestRicciEndAt (I := I) S clock x) W
      (hamiltonTestWNablaField (I := I) S clock W)
      (hamiltonTestWNabla2Field (I := I) S clock W)
      (hamiltonTestWTimeAt (I := I) S clock x W)
      ((1 / clock.elapsed : Real) • W clock.time x)
      (hamiltonTestRicciAt_symm (I := I) S clock x)
      (hamiltonTestRicciEndAt_inner (I := I) S clock x)
      (flowMetric_inner_hasDerivAt (I := I) S hS clock ht x) hWtime
      (hamiltonTestWNablaField_realizes (I := I) S clock W)
      (hamiltonTestWNabla2Field_realizes (I := I) S clock W)
      (flowG_connection_smooth (I := I) S clock.time) basis horth
      (hamiltonTestW_fixed_heat (I := I) S clock x basis horth W)
  have hWNabla : hamiltonTestWNablaField (I := I) S clock W x = 0 := by
    simpa only [hamiltonTestWNablaField,
      CanonicalSpatialDerivs0S.ofSmoothConnection,
      totalNabla0S_apply] using hDW
  have hWcurry (e : Fin n) :
      tensor0SCurry (I := I) (M := M) 1 x
          (hamiltonTestWNablaField (I := I) S clock W x) (basis e) = 0 := by
    rw [hWNabla]
    ext v
    simp
  have hsumZero :
      (∑ e : Fin n,
        inner0S (I := I) ((flowG (I := I) S).metric clock.time) x 1
          (tensor0SCurry (I := I) (M := M) 1 x
            (hamiltonTestWNablaField (I := I) S clock W x) (basis e))
          (tensor0SCurry (I := I) (M := M) 1 x
            (hamiltonTestWNablaField (I := I) S clock W x) (basis e))) = 0 := by
    simp only [hWcurry]
    simp [inner0S, MetricFiberData.inner]
  have hinnerSmul :
      inner0S (I := I) ((flowG (I := I) S).metric clock.time) x 1
          ((1 / clock.elapsed : Real) • W clock.time x) (W clock.time x) =
        (1 / clock.elapsed) *
          normSq0S (I := I) ((flowG (I := I) S).metric clock.time) x 1
            (W clock.time x) := by
    simp [inner0S, normSq0S, MetricFiberData.inner]
  refine ⟨d, htime, ?_⟩
  rw [hevolution, hinnerSmul, hsumZero]
  ring

omit [SigmaCompactSpace M] in
private theorem hamiltonTestW_normSq_gradient_eq_zero
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (W : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (hDW : totalNabla0SFun (I := I) (M := M) 1
      (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (W clock.time) x = 0) :
    gradientFun (I := I) (S.base.metric clock.time)
      (fun y : M => normSq0S (I := I) (S.base.metric clock.time) y 1
        (W clock.time y)) x = 0 := by
  let g := S.base.metric clock.time
  let cov := metricCov (I := I) (M := M) g
  let nablaW := hamiltonTestWNablaField (I := I) S clock W
  have hcomp (a : M) (j : Fin (Module.finrank Real E)) :
      ContMDiffOn I 𝓘(Real, Real) ∞
        (fun y : M => W clock.time y
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) a j y))
        (chartAt H a).source := by
    intro y hy
    refine ContMDiffAt.contMDiffWithinAt ?_
    have hvec : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (fun z : M =>
          Bundle.TotalSpace.mk' E z
            (chartBasisVecFiber (I := I) a j z)) y :=
      (chartBasisVec_contMDiffOn (I := I) a j).contMDiffAt
        ((trivializationAt E (TangentSpace I) a).open_baseSet.mem_nhds (by
          rw [trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M)]
          exact hy))
    exact TensorMultilinear.contMDiffAt_section_apply
      (𝕜 := Real) (I := I) (M := M) (n := 1) (x₀ := y) (T := W clock.time)
      ((W clock.time).contMDiff y)
      (v := fun _ : Fin 1 => fun z : M => chartBasisVecFiber (I := I) a j z)
      (fun _ => hvec)
  let Ysharp : (y : M) → TangentSpace I y := fun y =>
    cotangentSharp (I := I) g y (W clock.time y)
  have hY : MDiffAt (T% Ysharp) x := by
    simpa only [Ysharp] using
      cotangentSharp_gen_mdiffAt (I := I) g hcomp x
  have hmc : IsMetricCompatible (I := I) cov g := by
    simpa only [cov, g, metricCov] using
      leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) (S.base.metric clock.time)
  have hreal : TotalNabla0SRealizes 1 cov (W clock.time) nablaW := by
    simpa only [cov, g, nablaW, flowG, SolutionFamily.connection, metricCov] using
      hamiltonTestWNablaField_realizes (I := I) S clock W
  have hnabla : nablaW x = 0 := by
    simpa only [cov, g, nablaW, hamiltonTestWNablaField,
      CanonicalSpatialDerivs0S.ofSmoothConnection,
      totalNabla0S_apply] using hDW
  have hfun :
      (fun y : M => normSq0S (I := I) g y 1 (W clock.time y)) =
        fun y : M => g.inner y (Ysharp y) (Ysharp y) := by
    funext y
    rw [normSq0S_eq_inner, inner0S_one_eq_cotangent]
    rw [cotangentInner_eq_sharp]
  apply gradientFun_eq_zero_of_mfderiv_eq_zero (I := I)
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  have hXdiff : MDiffAt (T% fun y : M => X y) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hcovY : cov Ysharp x (X x) = 0 := by
    have hsharp := cotangentSharp_cov_eq_sharp_curry_of_mdiffAt
      (I := I) cov g hmc (W clock.time) nablaW hreal X x hY
    have hcurry :
        tensor0SCurry (I := I) (M := M) 1 x (nablaW x) (X x) = 0 := by
      rw [hnabla]
      simp only [map_zero, zero_apply]
    rw [hcurry] at hsharp
    have hzero : cotangentSharp (I := I) g x 0 = 0 := by
      change cotangentSharpLinear (I := I) g x 0 = 0
      exact map_zero _
    calc
      cov Ysharp x (X x) = cotangentSharp (I := I) g x 0 := by
        simpa only [Ysharp] using hsharp
      _ = 0 := hzero
  have hmetric := hmc.mvfderiv_inner (x := x) (X x) hY hY
  rw [hcovY] at hmetric
  rw [hfun]
  rw [← hX]
  apply (NormedSpace.fromTangentSpace (𝕜 := Real)
    (g.inner x (Ysharp x) (Ysharp x))).injective
  change mvfderiv (I := I)
    (fun y : M => g.inner y (Ysharp y) (Ysharp y)) x (X x) = 0
  simpa using hmetric

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem scalar_time_space_product_evolution
    {G : MetricConnectionFamily (I := I) (M := M) Real}
    {t : Real} {x : M}
    (c : Real -> Real) (h : M -> Real) (F : Real -> M -> Real)
    (c' dF LF : Real)
    (hc : HasDerivAt c c' t)
    (hFtime : HasDerivAt (fun r : Real => F r x) dF t)
    (hh : ContMDiff I 𝓘(Real, Real) ∞ h)
    (hFsmooth : ContMDiff I 𝓘(Real, Real) ∞ (F t))
    (hcross : (G.metric t).inner x
      (gradientFun (I := I) (G.metric t) h x)
      (gradientFun (I := I) (G.metric t) (F t) x) = 0)
    (hFheat : dF - laplacianAt (I := I) G t (F t) x = LF) :
    let q := fun r y => c r * (h y * F r y)
    let d := c' * (h x * F t x) + c t * (h x * dF)
    HasDerivAt (fun r : Real => q r x) d t ∧
      d - laplacianAt (I := I) G t (q t) x =
        (c' * h x - c t * laplacianAt (I := I) G t h x) * F t x +
          c t * h x * LF := by
  dsimp only
  let q := fun r y => c r * (h y * F r y)
  let d := c' * (h x * F t x) + c t * (h x * dF)
  have htime : HasDerivAt (fun r : Real => q r x) d t := by
    convert (hc.mul (hFtime.const_mul (h x))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl) using 1
    all_goals rfl
  refine ⟨htime, ?_⟩
  have hprod : ContMDiff I 𝓘(Real, Real) ∞
      (fun y : M => h y * F t y) := hh.mul hFsmooth
  have hlapProduct := laplacianAt_mul_of_scalarRegular (I := I) (x := x) G t
    (hh.mdifferentiable (by simp))
    (hFsmooth.mdifferentiable (by simp))
    (fun y => gradientFun_mdiffAt (I := I) (G.metric t) hh y)
    (fun y => gradientFun_mdiffAt (I := I) (G.metric t) hFsmooth y)
  have hlapScale := laplacianAt_smul (I := I) G t (c t)
    (hprod.mdifferentiable (by simp))
    (gradientFun_mdiffAt (I := I) (G.metric t) hprod x)
  have hcross' : (G.metric t).inner x
      (gradientAt (I := I) G t h x) (gradientAt (I := I) G t (F t) x) = 0 := by
    simpa only [gradientAt] using hcross
  have hlap : laplacianAt (I := I) G t (q t) x =
      c t * (h x * laplacianAt (I := I) G t (F t) x +
        F t x * laplacianAt (I := I) G t h x) := by
    change laplacianAt (I := I) G t
      ((c t) • fun y : M => h y * F t y) x = _
    rw [hlapScale, hlapProduct, hcross']
    ring
  rw [hlap]
  linear_combination c t * h x * hFheat

omit [SigmaCompactSpace M] in
private theorem hamiltonKFixedHeatAt_realizes
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x)) :
    hamiltonKTimeDerivativeAt (I := I) S clock.time x basis -
        metricTrace0S2TensorInBasis (I := I) basis
          (identityInvMetric (Idx := Fin n))
          (hamiltonKNabla2Field (I := I) S clock.time x) +
      covariantEndomorphismAction0S (I := I)
        (hamiltonKField (I := I) S clock.time x)
        (hamiltonTestRicciEndAt (I := I) S clock x) =
      hamiltonKFixedHeatAt (I := I) S clock x basis := by
  rfl

omit [SigmaCompactSpace M] in
private theorem hamiltonK_test_tensor_scalar_evolution
    [I.Boundaryless]
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (U : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (hUtime : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r : Real => U r x v)
        (hamiltonTestUTimeAt (I := I) S clock x U v) clock.time) :
    ∃ d : Real,
      HasDerivAt (fun r : Real => hamiltonKTestScalar (I := I) S U r x)
          d clock.time ∧
        d - laplacianAt (I := I) (flowG (I := I) S) clock.time
            (fun y => hamiltonKTestScalar (I := I) S U clock.time y) x =
          hamiltonKTestScalarHeatAt (I := I) S clock x basis U := by
  classical
  exact inner0S_square_time_deriv_sub_laplacianAt_of_fixed_heat_zero
      (I := I) (Idx := Fin n) (s := 2) (G := flowG (I := I) S)
      (t := clock.time) (x := x)
      (hamiltonTestRicciAt (I := I) S clock x)
      (hamiltonTestRicciEndAt (I := I) S clock x)
      (fun r => hamiltonKField (I := I) S r)
      (hamiltonKNablaField (I := I) S clock.time)
      (hamiltonKNabla2Field (I := I) S clock.time) U
      (hamiltonTestUNablaField (I := I) S clock.time U)
      (hamiltonTestUNabla2Field (I := I) S clock.time U)
      (hamiltonKTimeDerivativeAt (I := I) S clock.time x basis)
      (hamiltonTestUTimeAt (I := I) S clock x U)
      (hamiltonKFixedHeatAt (I := I) S clock x basis)
      (hamiltonTestRicciAt_symm (I := I) S clock x)
      (hamiltonTestRicciEndAt_inner (I := I) S clock x)
      (flowMetric_inner_hasDerivAt (I := I) S hS clock ht x)
      (hamiltonKTimeDerivativeAt_realizes (I := I) S hS clock ht x basis horth)
      hUtime (hamiltonKNablaField_realizes (I := I) S clock.time)
      (hamiltonKNabla2Field_realizes (I := I) S clock.time)
      (hamiltonTestUNablaField_realizes (I := I) S clock.time U)
      (hamiltonTestUNabla2Field_realizes (I := I) S clock.time U)
      (flowG_connection_smooth (I := I) S clock.time) basis horth
      (hamiltonTestU_fixed_heat_zero (I := I) S clock x basis horth U)
      (hamiltonKFixedHeatAt_realizes (I := I) S clock x basis)
      (hamiltonKNablaField_curry_finAddFlip
        (I := I) S clock.time x basis horth)

omit [SigmaCompactSpace M] in
private theorem hamiltonP_test_tensor_scalar_evolution
    [I.Boundaryless]
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (U : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (W : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (hUtime : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r : Real => U r x v)
        (hamiltonTestUTimeAt (I := I) S clock x U v) clock.time)
    (hWtime : ∀ v : Fin 1 → TangentSpace I x,
      HasDerivAt (fun r : Real => W r x v)
        (hamiltonTestWTimeAt (I := I) S clock x W v) clock.time) :
    ∃ d : Real,
      HasDerivAt (fun r : Real =>
        hamiltonPTestScalar (I := I) S U W r x) d clock.time ∧
      d - laplacianAt (I := I) (flowG (I := I) S) clock.time
          (fun y => hamiltonPTestScalar (I := I) S U W clock.time y) x =
        hamiltonPTestScalarHeatAt (I := I) S clock x basis U W := by
  classical
  exact inner0S_product_time_deriv_sub_laplacianAt_of_fixed_heats
    (I := I) (p := 2) (q := 1) (Idx := Fin n)
    (G := flowG (I := I) S) (t := clock.time) (x := x)
    (hamiltonTestRicciAt (I := I) S clock x)
    (hamiltonTestRicciEndAt (I := I) S clock x)
    (fun r => hamiltonPField (I := I) (S.base.metric r))
    (hamiltonPNablaField (I := I) S clock.time)
    (hamiltonPNabla2Field (I := I) S clock.time) U
    (hamiltonTestUNablaField (I := I) S clock.time U)
    (hamiltonTestUNabla2Field (I := I) S clock.time U) W
    (hamiltonTestWNablaField (I := I) S clock W)
    (hamiltonTestWNabla2Field (I := I) S clock W)
    (hamiltonPTimeDerivativeAt (I := I) S clock.time x basis)
    (hamiltonTestUTimeAt (I := I) S clock x U)
    (hamiltonTestWTimeAt (I := I) S clock x W)
    (hamiltonPFixedHeatAt (I := I) S clock x basis) 0
    ((1 / clock.elapsed : Real) • W clock.time x)
    (hamiltonTestRicciAt_symm (I := I) S clock x)
    (hamiltonTestRicciEndAt_inner (I := I) S clock x)
    (flowMetric_inner_hasDerivAt (I := I) S hS clock ht x)
    (hamiltonPTimeDerivativeAt_realizes
      (I := I) S hS clock ht x basis) hUtime hWtime
    (hamiltonPNablaField_realizes (I := I) S clock.time)
    (hamiltonPNabla2Field_realizes (I := I) S clock.time)
    (hamiltonTestUNablaField_realizes (I := I) S clock.time U)
    (hamiltonTestUNabla2Field_realizes (I := I) S clock.time U)
    (hamiltonTestWNablaField_realizes (I := I) S clock W)
    (hamiltonTestWNabla2Field_realizes (I := I) S clock W)
    (flowG_connection_smooth (I := I) S clock.time) basis horth rfl
    (hamiltonTestU_fixed_heat_zero (I := I) S clock x basis horth U)
    (hamiltonTestW_fixed_heat (I := I) S clock x basis horth W)

omit [SigmaCompactSpace M] in
private theorem hamiltonM_test_tensor_scalar_evolution
    [I.Boundaryless]
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (W : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (hWtime : ∀ v : Fin 1 → TangentSpace I x,
      HasDerivAt (fun r : Real => W r x v)
        (hamiltonTestWTimeAt (I := I) S clock x W v) clock.time) :
    ∃ d : Real,
      HasDerivAt (fun r : Real =>
        hamiltonMTestScalar (I := I) S clock W r x) d clock.time ∧
      d - laplacianAt (I := I) (flowG (I := I) S) clock.time
          (fun y => hamiltonMTestScalar (I := I) S clock W clock.time y) x =
        hamiltonMTestScalarHeatAt (I := I) S clock x basis W := by
  classical
  exact inner0S_product_time_deriv_sub_laplacianAt_of_fixed_heats
    (I := I) (p := 1) (q := 1) (Idx := Fin n)
    (G := flowG (I := I) S) (t := clock.time) (x := x)
    (hamiltonTestRicciAt (I := I) S clock x)
    (hamiltonTestRicciEndAt (I := I) S clock x)
    (fun r => hamiltonMFamilyField (I := I) clock.origin r
      (S.base.metric r))
    (hamiltonMNablaField (I := I) S clock)
    (hamiltonMNabla2Field (I := I) S clock) W
    (hamiltonTestWNablaField (I := I) S clock W)
    (hamiltonTestWNabla2Field (I := I) S clock W) W
    (hamiltonTestWNablaField (I := I) S clock W)
    (hamiltonTestWNabla2Field (I := I) S clock W)
    (hamiltonMTimeDerivativeAt (I := I) S clock x basis)
    (hamiltonTestWTimeAt (I := I) S clock x W)
    (hamiltonTestWTimeAt (I := I) S clock x W)
    (hamiltonMFixedHeatAt (I := I) S clock x basis)
    ((1 / clock.elapsed : Real) • W clock.time x)
    ((1 / clock.elapsed : Real) • W clock.time x)
    (hamiltonTestRicciAt_symm (I := I) S clock x)
    (hamiltonTestRicciEndAt_inner (I := I) S clock x)
    (flowMetric_inner_hasDerivAt (I := I) S hS clock ht x)
    (hamiltonMTimeDerivativeAt_realizes
      (I := I) S hS clock ht x basis horth) hWtime hWtime
    (hamiltonMNablaField_realizes (I := I) S clock)
    (hamiltonMNabla2Field_realizes (I := I) S clock)
    (hamiltonTestWNablaField_realizes (I := I) S clock W)
    (hamiltonTestWNabla2Field_realizes (I := I) S clock W)
    (hamiltonTestWNablaField_realizes (I := I) S clock W)
    (hamiltonTestWNabla2Field_realizes (I := I) S clock W)
    (flowG_connection_smooth (I := I) S clock.time) basis horth rfl
    (hamiltonTestW_fixed_heat (I := I) S clock x basis horth W)
    (hamiltonTestW_fixed_heat (I := I) S clock x basis horth W)

omit [SigmaCompactSpace M] in
theorem hamilton_harnack_block_exact_evolution_of_tensor_test_jet
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) {n : Nat}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (U_tensor : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (W : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (hUskew : ∀ X Y : TangentSpace I x,
      U_tensor clock.time x ![X, Y] = -U_tensor clock.time x ![Y, X])
    (hDW : totalNabla0SFun (I := I) (M := M) 1
      (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (W clock.time) x = 0)
    (hDU : ∀ X Y Z : TangentSpace I x,
      totalNabla0SFun (I := I) (M := M) 2
          (metricCov (I := I) (M := M) (S.base.metric clock.time))
          (U_tensor clock.time) x ![X, Y, Z] =
        (1 / 2 : Real) *
            (metricRicci (I := I) (M := M) (S.base.metric clock.time) x
                ![X, Y] * W clock.time x (fun _ : Fin 1 => Z) -
              metricRicci (I := I) (M := M) (S.base.metric clock.time) x
                ![X, Z] * W clock.time x (fun _ : Fin 1 => Y)) +
          (1 / (4 * clock.elapsed) : Real) *
            ((S.base.metric clock.time).inner x X Y *
                W clock.time x (fun _ : Fin 1 => Z) -
              (S.base.metric clock.time).inner x X Z *
                W clock.time x (fun _ : Fin 1 => Y)))
    (hUtime : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r : Real => U_tensor r x v)
        ((Geometry.Operator.roughLap0STensor (I := I)
            (S.base.metric clock.time)
            ((CanonicalSpatialDerivs0S.ofSmoothConnection
              (I := I)
              (metricCov (I := I) (M := M) (S.base.metric clock.time))
              (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
              (U_tensor clock.time)).nabla2A x) -
          covariantEndomorphismAction0S (I := I) (U_tensor clock.time x)
            (ricciEndAt (I := I) (S.base.metric clock.time)
              (metricRicci (I := I) (M := M)
                (S.base.metric clock.time) x)).toContinuousLinearMap) v)
        clock.time)
    (hWtime : ∀ v : Fin 1 → TangentSpace I x,
      HasDerivAt (fun r : Real => W r x v)
        ((Geometry.Operator.roughLap0STensor (I := I)
              (S.base.metric clock.time)
              ((CanonicalSpatialDerivs0S.ofSmoothConnection
                (I := I)
                (metricCov (I := I) (M := M) (S.base.metric clock.time))
                (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
                (W clock.time)).nabla2A x) +
            (1 / clock.elapsed : Real) • W clock.time x -
          covariantEndomorphismAction0S (I := I) (W clock.time x)
            (ricciEndAt (I := I) (S.base.metric clock.time)
              (metricRicci (I := I) (M := M)
                (S.base.metric clock.time) x)).toContinuousLinearMap) v)
        clock.time) :
    let q := fun r y =>
      inner0S (I := I) (S.base.metric r) y 4
          (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
            (S.base.rm04 r) y)
          ((U_tensor r y).product (U_tensor r y)) +
        2 * inner0S (I := I) (S.base.metric r) y 3
          (hamiltonPField (I := I) (S.base.metric r) y)
          ((U_tensor r y).product (W r y)) +
        inner0S (I := I) (S.base.metric r) y 2
          (hamiltonMOriginField (I := I) clock.origin r
            (S.base.metric r) y)
          ((W r y).product (W r y))
    HasDerivAt (fun r : Real => q r x)
        (deriv (fun r : Real => q r x) clock.time) clock.time ∧
      deriv (fun r : Real => q r x) clock.time -
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (q clock.time) x =
        hamiltonBlockJ
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (basis a) (basis b) (basis d) (basis c)))
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (basis a) (basis b) (basis c)))
            (fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
              (S.base.metric clock.time) x
                (vec2 (I := I) (basis a) (basis b)))
            (fun a b => U_tensor clock.time x
              (vec2 (I := I) (basis a) (basis b)))
            (fun a => W clock.time x (fun _ : Fin 1 => basis a)) +
          hamiltonBlockSigmaSquare
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (basis a) (basis b) (basis d) (basis c)))
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (basis a) (basis b) (basis c)))
            (fun a b => U_tensor clock.time x
              (vec2 (I := I) (basis a) (basis b)))
            (fun a => W clock.time x (fun _ : Fin 1 => basis a)) := by
  classical
  dsimp only
  obtain ⟨dK, hKtimeRaw, hKheat⟩ :=
    hamiltonK_test_tensor_scalar_evolution
      (I := I) S hS clock ht x basis horth U_tensor hUtime
  have hKtime := hKtimeRaw.congr_deriv hKtimeRaw.deriv.symm
  rw [← hKtimeRaw.deriv] at hKheat
  obtain ⟨dP, hPtimeRaw, hPheat⟩ :=
    hamiltonP_test_tensor_scalar_evolution
      (I := I) S hS clock ht x basis horth U_tensor W hUtime hWtime
  have hPtime := hPtimeRaw.congr_deriv hPtimeRaw.deriv.symm
  rw [← hPtimeRaw.deriv] at hPheat
  obtain ⟨dM, hMtimeRaw, hMheat⟩ :=
    hamiltonM_test_tensor_scalar_evolution
      (I := I) S hS clock ht x basis horth W hWtime
  have hMtime := hMtimeRaw.congr_deriv hMtimeRaw.deriv.symm
  rw [← hMtimeRaw.deriv] at hMheat
  have hKSmooth : ContMDiff I 𝓘(Real, Real) ∞
      (hamiltonKTestScalar (I := I) S U_tensor clock.time) := by
    change ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      inner0S (I := I) (S.base.metric clock.time) y 4
        (hamiltonKField (I := I) S clock.time y)
        ((U_tensor clock.time y).product (U_tensor clock.time y)))
    simpa only [Nat.reduceAdd] using
      (inner0S_product_contMDiff (I := I) (S.base.metric clock.time)
        (hamiltonKField (I := I) S clock.time)
        (U_tensor clock.time) (U_tensor clock.time))
  have hPSmooth : ContMDiff I 𝓘(Real, Real) ∞
      (hamiltonPTestScalar (I := I) S U_tensor W clock.time) := by
    change ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      inner0S (I := I) (S.base.metric clock.time) y 3
        (hamiltonPField (I := I) (S.base.metric clock.time) y)
        ((U_tensor clock.time y).product (W clock.time y)))
    simpa only [Nat.reduceAdd] using
      (inner0S_product_contMDiff (I := I) (S.base.metric clock.time)
        (hamiltonPField (I := I) (S.base.metric clock.time))
        (U_tensor clock.time) (W clock.time))
  have hMSmooth : ContMDiff I 𝓘(Real, Real) ∞
      (hamiltonMTestScalar (I := I) S clock W clock.time) := by
    change ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      inner0S (I := I) (S.base.metric clock.time) y 2
        (hamiltonMOriginField (I := I) clock.origin clock.time
          (S.base.metric clock.time) y)
        ((W clock.time y).product (W clock.time y)))
    simpa only [Nat.reduceAdd] using
      (inner0S_product_contMDiff (I := I) (S.base.metric clock.time)
        (hamiltonMOriginField (I := I) clock.origin clock.time
          (S.base.metric clock.time))
        (W clock.time) (W clock.time))
  have hrows := hamiltonBlock_scalar_row_sum
    (I := I) (G := flowG (I := I) S) (t := clock.time) (x := x)
    (hamiltonKTestScalar (I := I) S U_tensor)
    (hamiltonPTestScalar (I := I) S U_tensor W)
    (hamiltonMTestScalar (I := I) S clock W)
    (hamiltonKTestScalarHeatAt (I := I) S clock x basis U_tensor)
    (hamiltonPTestScalarHeatAt (I := I) S clock x basis U_tensor W)
    (hamiltonMTestScalarHeatAt (I := I) S clock x basis W)
    hKtime hPtime hMtime hKSmooth hPSmooth hMSmooth hKheat hPheat hMheat
  constructor
  · change HasDerivAt (fun r : Real =>
      hamiltonKTestScalar (I := I) S U_tensor r x +
        2 * hamiltonPTestScalar (I := I) S U_tensor W r x +
        hamiltonMTestScalar (I := I) S clock W r x)
      (deriv (fun r : Real =>
        hamiltonKTestScalar (I := I) S U_tensor r x +
          2 * hamiltonPTestScalar (I := I) S U_tensor W r x +
          hamiltonMTestScalar (I := I) S clock W r x) clock.time) clock.time
    exact hrows.1
  · change deriv (fun r : Real =>
        hamiltonKTestScalar (I := I) S U_tensor r x +
          2 * hamiltonPTestScalar (I := I) S U_tensor W r x +
          hamiltonMTestScalar (I := I) S clock W r x) clock.time -
        laplacianAt (I := I) (flowG (I := I) S) clock.time
          (fun y =>
            hamiltonKTestScalar (I := I) S U_tensor clock.time y +
              2 * hamiltonPTestScalar (I := I) S U_tensor W clock.time y +
              hamiltonMTestScalar (I := I) S clock W clock.time y) x = _
    calc
      _ = hamiltonKTestScalarHeatAt (I := I) S clock x basis U_tensor +
          2 * hamiltonPTestScalarHeatAt
            (I := I) S clock x basis U_tensor W +
          hamiltonMTestScalarHeatAt (I := I) S clock x basis W := hrows.2
      _ = hamiltonBlockRawProduct
          (fun a b c d => hamiltonKField (I := I) S clock.time x
            (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
          (fun a b c => hamiltonPField (I := I)
            (S.base.metric clock.time) x
              (vec3 (I := I) (basis a) (basis b) (basis c)))
          (fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
            (S.base.metric clock.time) x
              (vec2 (I := I) (basis a) (basis b)))
          (fun a b c d => hamiltonKFixedHeatAt (I := I) S clock x basis
            (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
          (fun a b c => hamiltonPFixedHeatAt (I := I) S clock x basis
            (vec3 (I := I) (basis a) (basis b) (basis c)))
          (fun a b => hamiltonMFixedHeatAt (I := I) S clock x basis
            (vec2 (I := I) (basis a) (basis b)))
          (fun e a b c d => hamiltonKNablaField (I := I) S clock.time x
            (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d)))
          (fun e a b c => hamiltonPNablaField (I := I) S clock.time x
            (vec4 (I := I) (basis e) (basis a) (basis b) (basis c)))
          (fun e a b => hamiltonTestUNablaField
            (I := I) S clock.time U_tensor x
              (vec3 (I := I) (basis e) (basis a) (basis b)))
          (fun a => ((1 / clock.elapsed : Real) • W clock.time x)
            (fun _ : Fin 1 => basis a))
          (fun a b => U_tensor clock.time x
            (vec2 (I := I) (basis a) (basis b)))
          (fun a => W clock.time x (fun _ : Fin 1 => basis a)) := by
        have hWNabla :
            hamiltonTestWNablaField (I := I) S clock W x = 0 := by
          simpa only [hamiltonTestWNablaField,
            CanonicalSpatialDerivs0S.ofSmoothConnection,
            totalNabla0S_apply] using hDW
        have hWcurry (e : Fin n) :
            tensor0SCurry (I := I) (M := M) 1 x
                (hamiltonTestWNablaField (I := I) S clock W x) (basis e) = 0 := by
          rw [hWNabla]
          ext v
          simp
        have hzeroProductLeft {p q : Nat}
            (A : Tensor0SSpace q I x) :
            (0 : Tensor0SSpace p I x).product A = 0 := by
          ext v
          simp [Tensor0SSpace.product_apply]
        have hzeroProductRight {p q : Nat}
            (A : Tensor0SSpace p I x) :
            A.product (0 : Tensor0SSpace q I x) = 0 := by
          ext v
          simp [Tensor0SSpace.product_apply]
        have hinnerZero {s : Nat} (A : Tensor0SSpace s I x) :
            inner0S (I := I) (S.base.metric clock.time) x s A 0 = 0 := by
          simp [inner0S, MetricFiberData.inner]
        have hinv := metricInverseInBasis_of_orthonormal
          (I := I) (S.base.metric clock.time) basis horth
        have hMcomm := inner0S_product_comm_one_of_finAddFlip
          (I := I) (S.base.metric clock.time) basis hinv
          (hamiltonMOriginField (I := I) clock.origin clock.time
            (S.base.metric clock.time) x)
          ((1 / clock.elapsed : Real) • W clock.time x) (W clock.time x)
          (hamiltonMOriginField_finAddFlip
            (I := I) S hS clock ht x)
        rw [hamiltonBlockRawProduct_eq_inner0S
          (I := I) (S.base.metric clock.time) basis horth]
        unfold hamiltonKTestScalarHeatAt hamiltonPTestScalarHeatAt
          hamiltonMTestScalarHeatAt inner0SSquareFixedHeatAt
          inner0SProductFixedHeatAt
        simp only [flowG, Nat.reduceAdd]
        simp only [hWcurry, hzeroProductLeft, hzeroProductRight,
          add_zero, hinnerZero, Finset.sum_const_zero,
          mul_zero, sub_zero]
        rw [← hMcomm]
        ring
      _ = hamiltonBlockJ
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (basis a) (basis b) (basis d) (basis c)))
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (basis a) (basis b) (basis c)))
            (fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
              (S.base.metric clock.time) x
                (vec2 (I := I) (basis a) (basis b)))
            (fun a b => U_tensor clock.time x
              (vec2 (I := I) (basis a) (basis b)))
            (fun a => W clock.time x (fun _ : Fin 1 => basis a)) +
          hamiltonBlockSigmaSquare
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (basis a) (basis b) (basis d) (basis c)))
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (basis a) (basis b) (basis c)))
            (fun a b => U_tensor clock.time x
              (vec2 (I := I) (basis a) (basis b)))
            (fun a => W clock.time x (fun _ : Fin 1 => basis a)) := by
        let R : Fin n → Fin n → Fin n → Fin n → Real := fun a b c d =>
          S.base.rm04 clock.time x
            (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))
        let Ric : Fin n → Fin n → Real := fun a b =>
          metricRicci (I := I) (M := M) (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b))
        let nablaR : Fin n → Fin n → Fin n → Fin n → Fin n → Real :=
          fun e a b c d => nablaRm04Field (I := I) S clock.time x
            (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d))
        let nablaRic : Fin n → Fin n → Fin n → Real := fun a b c =>
          metricNablaRic (I := I) (M := M) (S.base.metric clock.time) x
            (vec3 (I := I) (basis a) (basis b) (basis c))
        let nablaP : Fin n → Fin n → Fin n → Fin n → Real := fun e a b c =>
          hamiltonNablaPField (I := I) (S.base.metric clock.time) x
            (vec4 (I := I) (basis e) (basis a) (basis b) (basis c))
        let nablaM : Fin n → Fin n → Fin n → Real := fun e a b =>
          hamiltonMNablaField (I := I) S clock x
            (vec3 (I := I) (basis e) (basis a) (basis b))
        let Uc : Fin n → Fin n → Real := fun a b =>
          U_tensor clock.time x (vec2 (I := I) (basis a) (basis b))
        let Wc : Fin n → Real := fun a =>
          W clock.time x (fun _ : Fin 1 => basis a)
        have hRm : Rm04Symm R := by
          simpa only [R] using
            (hamilton_rm_components_symm
              (I := I) S ⟨clock.time, ht⟩ x basis)
        have hNablaRm : ∀ e, Rm04PairSymm (nablaR e) := by
          simpa only [nablaR] using
            (hamilton_nabla_rm_components_pair_symm
              (I := I) S clock.time x basis horth)
        have hRic : ∀ a b, Ric a b = Ric b a := by
          intro a b
          exact metricRicciAt_symm (I := I) (S.base.metric clock.time) x
            (basis a) (basis b)
        have hNablaRic : ∀ a b c, nablaRic a b c = nablaRic a c b := by
          intro a b c
          exact metricNablaRic_last_two_symm
            (I := I) (M := M) (S.base.metric clock.time) x
              (basis a) (basis b) (basis c)
        have hTrace : curvatureRicciTraceComponents R Ric := by
          simpa only [R, Ric] using
            (hamilton_curvature_ricci_trace_components
              (I := I) S ⟨clock.time, ht⟩ x basis horth)
        have hContract :
            contractedCurvatureDerivativeComponents nablaR nablaRic := by
          simpa only [nablaR, nablaRic] using
            (hamilton_contracted_curvature_derivative_components
              (I := I) S clock.time x basis horth)
        have hNablaPSkew : ∀ e a b c,
            nablaP e a b c = -nablaP e b a c := by
          intro e a b c
          simp only [nablaP, hamiltonNablaPField_apply]
          ring
        have hinv := metricInverseInBasis_of_orthonormal
          (I := I) (S.base.metric clock.time) basis horth
        have hdiv (a b : Fin n) :
            hamiltonDivPAt (I := I) (S.base.metric clock.time) x
                (vec2 (I := I) (basis a) (basis b)) =
              ∑ e, nablaP e e a b := by
          have h := hamiltonDivPAt_apply_eq_trace_hamiltonNablaP
            (I := I) (S.base.metric clock.time) basis
              (identityInvMetric (Idx := Fin n)) hinv (basis a) (basis b)
          simp only [identityInvMetric, diagonalInvMetric, ite_mul, one_mul,
            zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
          simpa only [nablaP] using h
        have hdivfun :
            (fun a b => ∑ e, nablaP e e a b) =
              fun a b => hamiltonDivPAt (I := I)
                (S.base.metric clock.time) x
                  (vec2 (I := I) (basis a) (basis b)) := by
          funext a b
          exact (hdiv a b).symm
        have hMfield :
            hamiltonMOriginField (I := I) clock.origin clock.time
                (S.base.metric clock.time) x =
              hamiltonMAt (I := I) clock (S.base.metric clock.time) x := by
          simpa only [hamiltonMField] using
            (hamiltonMField_apply (I := I) S hS clock ht x)
        have hMcomponent (a b : Fin n) :
            hamiltonMComponent clock R Ric
                (fun i j => ∑ e, nablaP e e i j) a b =
              hamiltonMOriginField (I := I) clock.origin clock.time
                (S.base.metric clock.time) x
                  (vec2 (I := I) (basis a) (basis b)) := by
          rw [hdivfun]
          have hRmetric : R = fun i j k l =>
              metricRm04 (I := I) (M := M) (S.family.metric clock.time) x
                (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) := by
            rfl
          have hRicmetric : Ric = fun i j =>
              metricRicci (I := I) (M := M) (S.family.metric clock.time) x
                (vec2 (I := I) (basis i) (basis j)) := by
            rfl
          have hDivmetric :
              (fun i j => hamiltonDivPAt (I := I)
                (S.base.metric clock.time) x
                  (vec2 (I := I) (basis i) (basis j))) =
                fun i j => hamiltonDivPAt (I := I)
                  (S.family.metric clock.time) x
                    (vec2 (I := I) (basis i) (basis j)) := by
            rfl
          have hcanon := hamiltonMComponent_eq_hamiltonMAt_orthonormal
            (I := I) S hS clock ht x basis horth a b
          have happ := congrArg (fun T : Tensor0SSpace 2 I x =>
            T (vec2 (I := I) (basis a) (basis b))) hMfield
          rw [hRmetric, hRicmetric, hDivmetric]
          exact hcanon.trans happ.symm
        have hM : ∀ a b,
            hamiltonMComponent clock R Ric
                (fun i j => ∑ e, nablaP e e i j) a b =
              hamiltonMComponent clock R Ric
                (fun i j => ∑ e, nablaP e e i j) b a := by
          intro a b
          rw [hMcomponent, hMcomponent]
          have hab := congrArg (fun T : Tensor0SSpace 2 I x =>
            T (vec2 (I := I) (basis a) (basis b))) hMfield
          have hba := congrArg (fun T : Tensor0SSpace 2 I x =>
            T (vec2 (I := I) (basis b) (basis a))) hMfield
          exact hab.trans ((hamiltonMAt_symm
            (I := I) S clock ht x (basis a) (basis b)).trans hba.symm)
        have hU : ∀ a b, Uc a b = -Uc b a := by
          intro a b
          change U_tensor clock.time x
              (vec2 (I := I) (basis a) (basis b)) =
            -U_tensor clock.time x
              (vec2 (I := I) (basis b) (basis a))
          have hv (X Y : TangentSpace I x) :
              vec2 (I := I) X Y = ![X, Y] := by
            funext i
            fin_cases i <;> rfl
          simpa only [hv] using hUskew (basis a) (basis b)
        have hKcomp (a b c d : Fin n) :
            hamiltonKField (I := I) S clock.time x
                (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) =
              R a b d c := by
          simp only [hamiltonKField, R, Tensor0SField.domDomCongr_apply,
            Tensor0SSpace.domDomCongr_apply]
          congr 1
          funext i
          fin_cases i <;> rfl
        have hPcomp (a b c : Fin n) :
            hamiltonPField (I := I) (S.base.metric clock.time) x
                (vec3 (I := I) (basis a) (basis b) (basis c)) =
              hamiltonPComponent nablaRic a b c := by
          simp only [hamiltonPField_apply, hamiltonPAt_apply,
            hamiltonPComponent, nablaRic]
        have hLKcomp (a b c d : Fin n) :
            hamiltonKFixedHeatAt (I := I) S clock x basis
                (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)) =
              hamiltonRmReactionComponent R a b d c := by
          simpa only [hamiltonKFixedHeatAt, hamiltonKTimeDerivativeAt,
            hamiltonKNabla2Field, hamiltonTestRicciEndAt,
            hamiltonTestRicciAt, R] using
            (hamiltonK_fixedHeat_component
              (I := I) S ⟨clock.time, ht⟩ x basis horth hRm hTrace a b c d)
        have hLPcomp (a b c : Fin n) :
            hamiltonPFixedHeatAt (I := I) S clock x basis
                (vec3 (I := I) (basis a) (basis b) (basis c)) =
              hamiltonPEvolutionReactionComponent
                R Ric nablaR nablaRic a b c := by
          simpa only [R, Ric, nablaR, nablaRic] using
            (hamiltonPFixedHeatAt_component
              (I := I) S hS clock ht x basis horth a b c)
        have hLMcomp (a b : Fin n) :
            hamiltonMFixedHeatAt (I := I) S clock x basis
                (vec2 (I := I) (basis a) (basis b)) =
              hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
                (fun i j => ∑ e, nablaP e e i j) a b := by
          rw [hdivfun]
          simpa only [R, Ric, nablaRic, nablaP] using
            (hamiltonMFixedHeatAt_component
              (I := I) S hS clock ht x basis horth a b)
        have hDKcomp (e a b c d : Fin n) :
            hamiltonKNablaField (I := I) S clock.time x
                (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d)) =
              nablaR e a b d c := by
          simp only [hamiltonKNablaField, nablaR,
            Tensor0SField.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
          congr 1
          funext i
          fin_cases i <;> rfl
        have hPNabla :
            hamiltonPNablaField (I := I) S clock.time =
              hamiltonNablaPField (I := I) (S.base.metric clock.time) := by
          rfl
        have hDPcomp (e a b c : Fin n) :
            hamiltonPNablaField (I := I) S clock.time x
                (vec4 (I := I) (basis e) (basis a) (basis b) (basis c)) =
              nablaP e a b c := by
          rw [hPNabla]
        have hDUcomp (e a b : Fin n) :
            hamiltonTestUNablaField (I := I) S clock.time U_tensor x
                (vec3 (I := I) (basis e) (basis a) (basis b)) =
              hamiltonTestJetDU clock Ric
                (fun i j => if i = j then (1 : Real) else 0) Wc e a b := by
          change totalNabla0SFun (I := I) (M := M) 2
              (metricCov (I := I) (M := M) (S.base.metric clock.time))
              (U_tensor clock.time) x
                (vec3 (I := I) (basis e) (basis a) (basis b)) = _
          have hslots : vec3 (I := I) (basis e) (basis a) (basis b) =
              ![basis e, basis a, basis b] := by
            funext i
            fin_cases i <;> rfl
          rw [hslots]
          rw [hDU]
          simp only [hamiltonTestJetDU, Ric, Wc, horth]
          have hslotsEA : vec2 (I := I) (basis e) (basis a) =
              ![basis e, basis a] := by
            funext i
            fin_cases i <;> rfl
          have hslotsEB : vec2 (I := I) (basis e) (basis b) =
              ![basis e, basis b] := by
            funext i
            fin_cases i <;> rfl
          rw [← hslotsEA, ← hslotsEB]
        have hLWcomp (a : Fin n) :
            ((1 / clock.elapsed : Real) • W clock.time x)
                (fun _ : Fin 1 => basis a) =
              (1 / clock.elapsed) * Wc a := by
          simp only [Tensor0SSpace.smul_apply, smul_eq_mul, Wc]
        have hraw :
            hamiltonBlockRawProduct
                (fun a b c d => hamiltonKField (I := I) S clock.time x
                  (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
                (fun a b c => hamiltonPField (I := I)
                  (S.base.metric clock.time) x
                    (vec3 (I := I) (basis a) (basis b) (basis c)))
                (fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
                  (S.base.metric clock.time) x
                    (vec2 (I := I) (basis a) (basis b)))
                (fun a b c d => hamiltonKFixedHeatAt
                  (I := I) S clock x basis
                    (vec4 (I := I) (basis a) (basis b) (basis c) (basis d)))
                (fun a b c => hamiltonPFixedHeatAt (I := I) S clock x basis
                  (vec3 (I := I) (basis a) (basis b) (basis c)))
                (fun a b => hamiltonMFixedHeatAt (I := I) S clock x basis
                  (vec2 (I := I) (basis a) (basis b)))
                (fun e a b c d => hamiltonKNablaField
                  (I := I) S clock.time x
                    (vec5 (I := I) (basis e) (basis a) (basis b)
                      (basis c) (basis d)))
                (fun e a b c => hamiltonPNablaField
                  (I := I) S clock.time x
                    (vec4 (I := I) (basis e) (basis a) (basis b) (basis c)))
                (fun e a b => hamiltonTestUNablaField
                  (I := I) S clock.time U_tensor x
                    (vec3 (I := I) (basis e) (basis a) (basis b)))
                (fun a => ((1 / clock.elapsed : Real) • W clock.time x)
                  (fun _ : Fin 1 => basis a)) Uc Wc =
              hamiltonBlockRawProduct
                (fun a b c d => R a b d c) (hamiltonPComponent nablaRic)
                (hamiltonMComponent clock R Ric
                  (fun i j => ∑ e, nablaP e e i j))
                (fun a b c d => hamiltonRmReactionComponent R a b d c)
                (hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic)
                (hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
                  (fun i j => ∑ e, nablaP e e i j))
                (fun e a b c d => nablaR e a b d c) nablaP
                (hamiltonTestJetDU clock Ric
                  (fun i j => if i = j then (1 : Real) else 0) Wc)
                (fun a => (1 / clock.elapsed) * Wc a) Uc Wc := by
          unfold hamiltonBlockRawProduct
          simp_rw [hKcomp, hPcomp, ← hMcomponent, hLKcomp, hLPcomp,
            hLMcomp, hDKcomp, hDPcomp, hDUcomp, hLWcomp]
        rw [hraw]
        have hheatRaw := hamiltonBlock_heat_product_eq_raw
          (fun a b c d => R a b d c) (hamiltonPComponent nablaRic)
          (hamiltonMComponent clock R Ric (fun i j => ∑ e, nablaP e e i j))
          (fun a b c d => hamiltonRmReactionComponent R a b d c)
          (hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic)
          (hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
            (fun i j => ∑ e, nablaP e e i j))
          (fun e a b c d => nablaR e a b d c) nablaP nablaM
          (hamiltonTestJetDU clock Ric
            (fun i j => if i = j then (1 : Real) else 0) Wc)
          (fun _ => 0) (fun _ _ => 0)
          (fun a => (1 / clock.elapsed) * Wc a) Uc Wc
          (by simp) (by simp) hM
        rw [← hheatRaw]
        have hblock := hamiltonBlock_heat_product_eq_j_add_sigma_square
          clock R Ric nablaR nablaRic nablaP nablaM Uc Wc hRm hNablaRm
          hRic hNablaRic hTrace hContract hNablaPSkew hM hU
        rw [hblock]
        have hPfun : hamiltonPComponent nablaRic = fun a b c =>
            hamiltonPField (I := I) (S.base.metric clock.time) x
              (vec3 (I := I) (basis a) (basis b) (basis c)) := by
          funext a b c
          exact (hPcomp a b c).symm
        have hMfun :
            hamiltonMComponent clock R Ric
                (fun i j => ∑ e, nablaP e e i j) =
              fun a b => hamiltonMOriginField (I := I)
                clock.origin clock.time (S.base.metric clock.time) x
                  (vec2 (I := I) (basis a) (basis b)) := by
          funext a b
          exact hMcomponent a b
        rw [hPfun, hMfun]

omit [SigmaCompactSpace M] in
theorem hamilton_harnack_block_exact_evolution
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) {n : Nat}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
    (W₀ : StrongDual Real (TangentSpace I x)) :
    ∃ (U_tensor : Real →
        Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
      (W : Real →
        Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1),
      U_tensor clock.time x = U₀.toTensor0S ∧
      (∀ Z : TangentSpace I x,
        W clock.time x (fun _ : Fin 1 => Z) = W₀ Z) ∧
      let q := fun r y =>
        inner0S (I := I) (S.base.metric r) y 4
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
              (S.base.rm04 r) y)
            ((U_tensor r y).product (U_tensor r y)) +
          2 * inner0S (I := I) (S.base.metric r) y 3
            (hamiltonPField (I := I) (S.base.metric r) y)
            ((U_tensor r y).product (W r y)) +
          inner0S (I := I) (S.base.metric r) y 2
            (hamiltonMOriginField (I := I) clock.origin r
              (S.base.metric r) y)
            ((W r y).product (W r y))
      HasDerivAt (fun r : Real => q r x)
          (deriv (fun r : Real => q r x) clock.time) clock.time ∧
        deriv (fun r : Real => q r x) clock.time -
            laplacianAt (I := I) (flowG (I := I) S) clock.time
              (q clock.time) x =
          hamiltonBlockJ
              (fun a b c d => S.base.rm04 clock.time x
                (vec4 (I := I) (basis a) (basis b) (basis d) (basis c)))
              (fun a b c => hamiltonPField (I := I)
                (S.base.metric clock.time) x
                  (vec3 (I := I) (basis a) (basis b) (basis c)))
              (fun a b => hamiltonMOriginField (I := I)
                clock.origin clock.time (S.base.metric clock.time) x
                  (vec2 (I := I) (basis a) (basis b)))
              (fun a b => U₀ ![basis a, basis b])
              (fun a => W₀ (basis a)) +
            hamiltonBlockSigmaSquare
              (fun a b c d => S.base.rm04 clock.time x
                (vec4 (I := I) (basis a) (basis b) (basis d) (basis c)))
              (fun a b c => hamiltonPField (I := I)
                (S.base.metric clock.time) x
                  (vec3 (I := I) (basis a) (basis b) (basis c)))
              (fun a b => U₀ ![basis a, basis b])
              (fun a => W₀ (basis a)) := by
  classical
  have hmc : IsMetricCompatible (I := I)
      (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (S.base.metric clock.time) := by
    simpa [metricCov] using
      leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) (S.base.metric clock.time)
  obtain ⟨U, U_tensor, W, hU_tensor, _, _, hUvalue, hWvalue,
      hDW, hDU, hUtime, hWtime⟩ :=
    hamilton_test_jet_realization
      (I := I)
      (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
      (S.base.metric clock.time) hmc x clock
      (metricRicci (I := I) (M := M) (S.base.metric clock.time) x) U₀ W₀
  have hDU' : ∀ X Y Z : TangentSpace I x,
      totalNabla0SFun (I := I) (M := M) 2
          (metricCov (I := I) (M := M) (S.base.metric clock.time))
          (U_tensor clock.time) x ![X, Y, Z] =
        (1 / 2 : Real) *
            (metricRicci (I := I) (M := M) (S.base.metric clock.time) x
                ![X, Y] * W clock.time x (fun _ : Fin 1 => Z) -
              metricRicci (I := I) (M := M) (S.base.metric clock.time) x
                ![X, Z] * W clock.time x (fun _ : Fin 1 => Y)) +
          (1 / (4 * clock.elapsed) : Real) *
            ((S.base.metric clock.time).inner x X Y *
                W clock.time x (fun _ : Fin 1 => Z) -
              (S.base.metric clock.time).inner x X Z *
                W clock.time x (fun _ : Fin 1 => Y)) := by
    intro X Y Z
    simpa only [hWvalue] using hDU X Y Z
  have hUskew (X Y : TangentSpace I x) :
      U_tensor clock.time x ![X, Y] =
        -U_tensor clock.time x ![Y, X] := by
    rw [← hU_tensor clock.time x]
    have hswap := (U clock.time x).map_swap (v := ![Y, X])
      (i := (0 : Fin 2)) (j := 1) (by decide)
    have hv : ![Y, X] ∘ Equiv.swap (0 : Fin 2) 1 = ![X, Y] := by
      funext q
      fin_cases q <;> simp
    rw [hv] at hswap
    exact hswap
  have hexact := hamilton_harnack_block_exact_evolution_of_tensor_test_jet
    (I := I) S hS clock ht x basis horth U_tensor W hUskew hDW hDU'
      hUtime hWtime
  have hUvalueTensor : U_tensor clock.time x = U₀.toTensor0S := by
    calc
      U_tensor clock.time x = (U clock.time x).toTensor0S :=
        (hU_tensor clock.time x).symm
      _ = U₀.toTensor0S := congrArg
        (HamiltonHarnackTwoForm.toTensor0S (I := I)) hUvalue
  have hUcomp (a b : Fin n) :
      U_tensor clock.time x (vec2 (I := I) (basis a) (basis b)) =
        U₀ ![basis a, basis b] := by
    rw [hUvalueTensor]
    simp only [HamiltonHarnackTwoForm.toTensor0S_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  refine ⟨U_tensor, W, hUvalueTensor, hWvalue, ?_⟩
  simpa only [hUcomp, hWvalue] using hexact

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem normSq0S_one_eq_sum_orthonormal
    {x : M} {n : Nat}
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace 1 I x) :
    normSq0S (I := I) g x 1 A =
      ∑ a : Fin n, (A (fun _ : Fin 1 => basis a)) ^ 2 := by
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [normSq0S_identity_eq_sum_sq (I := I) g x 1 basis hinv A,
    sum_fin_one_fun]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem normSq0S_two_eq_sum_orthonormal
    {x : M} {n : Nat}
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace 2 I x) :
    normSq0S (I := I) g x 2 A =
      ∑ a : Fin n, ∑ b : Fin n,
        (A (vec2 (I := I) (basis a) (basis b))) ^ 2 := by
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  rw [normSq0S_identity_eq_sum_sq (I := I) g x 2 basis hinv A,
    sum_fin_two_fun]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [component0S_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem sum_inner0S_curry_three_eq_sum_sq_orthonormal
    {x : M} {n : Nat}
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace 3 I x)
    (C : Fin n → Fin n → Fin n → Real)
    (hC : ∀ e a b,
      A (vec3 (I := I) (basis e) (basis a) (basis b)) = C e a b) :
    (∑ e : Fin n,
      inner0S (I := I) g x 2
        (tensor0SCurry (I := I) (M := M) 2 x A (basis e))
        (tensor0SCurry (I := I) (M := M) 2 x A (basis e))) =
      ∑ e : Fin n, ∑ a : Fin n, ∑ b : Fin n, (C e a b) ^ 2 := by
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis horth
  simp_rw [← normSq0S_eq_inner]
  rw [normSq0S_curry_sum (I := I) g x 2 basis hinv A,
    normSq0S_three_identity_eq_sum (I := I) g x basis hinv A]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [component0S_apply]
  exact (congrArg A (by
    funext i
    fin_cases i <;> rfl)).trans (hC e a b)

omit [SigmaCompactSpace M] in
private theorem hamilton_perturbed_harnack_block_exact_evolution_of_test_jet
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) {n : Nat}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (U : ∀ (_ : Real) (y : M),
      HamiltonHarnackTwoForm (TangentSpace I y))
    (U_tensor : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (W : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (hU_tensor : ∀ r y, (U r y).toTensor0S = U_tensor r y)
    (hDW : totalNabla0SFun (I := I) (M := M) 1
      (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (W clock.time) x = 0)
    (hDU : ∀ X Y Z : TangentSpace I x,
      totalNabla0SFun (I := I) (M := M) 2
          (metricCov (I := I) (M := M) (S.base.metric clock.time))
          (U_tensor clock.time) x ![X, Y, Z] =
        (1 / 2 : Real) *
            (metricRicci (I := I) (M := M) (S.base.metric clock.time) x
                ![X, Y] * W clock.time x (fun _ : Fin 1 => Z) -
              metricRicci (I := I) (M := M) (S.base.metric clock.time) x
                ![X, Z] * W clock.time x (fun _ : Fin 1 => Y)) +
          (1 / (4 * clock.elapsed) : Real) *
            ((S.base.metric clock.time).inner x X Y *
                W clock.time x (fun _ : Fin 1 => Z) -
              (S.base.metric clock.time).inner x X Z *
                W clock.time x (fun _ : Fin 1 => Y)))
    (hUtime : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r : Real => U_tensor r x v)
        ((Geometry.Operator.roughLap0STensor (I := I)
            (S.base.metric clock.time)
            ((CanonicalSpatialDerivs0S.ofSmoothConnection
              (I := I)
              (metricCov (I := I) (M := M) (S.base.metric clock.time))
              (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
              (U_tensor clock.time)).nabla2A x) -
          covariantEndomorphismAction0S (I := I) (U_tensor clock.time x)
            (ricciEndAt (I := I) (S.base.metric clock.time)
              (metricRicci (I := I) (M := M)
                (S.base.metric clock.time) x)).toContinuousLinearMap) v)
        clock.time)
    (hWtime : ∀ v : Fin 1 → TangentSpace I x,
      HasDerivAt (fun r : Real => W r x v)
        ((Geometry.Operator.roughLap0STensor (I := I)
              (S.base.metric clock.time)
              ((CanonicalSpatialDerivs0S.ofSmoothConnection
                (I := I)
                (metricCov (I := I) (M := M) (S.base.metric clock.time))
                (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
                (W clock.time)).nabla2A x) +
            (1 / clock.elapsed : Real) • W clock.time x -
          covariantEndomorphismAction0S (I := I) (W clock.time x)
            (ricciEndAt (I := I) (S.base.metric clock.time)
              (metricRicci (I := I) (M := M)
                (S.base.metric clock.time) x)).toContinuousLinearMap) v)
        clock.time)
    (a psi : Real → Real) (h : M → Real) (a' psi' : Real)
    (ha : HasDerivAt a a' clock.time)
    (hpsi : HasDerivAt psi psi' clock.time)
    (hh : ContMDiff I 𝓘(Real, Real) ∞ h) :
    let q := fun r y =>
      inner0S (I := I) (S.base.metric r) y 4
          (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
            (S.base.rm04 r) y)
          ((U_tensor r y).product (U_tensor r y)) +
        2 * inner0S (I := I) (S.base.metric r) y 3
          (hamiltonPField (I := I) (S.base.metric r) y)
          ((U_tensor r y).product (W r y)) +
        inner0S (I := I) (S.base.metric r) y 2
          (hamiltonMOriginField (I := I) clock.origin r
            (S.base.metric r) y)
          ((W r y).product (W r y)) +
        (a r / (r - clock.origin)) *
          (h y * normSq0S (I := I) (S.base.metric r) y 1 (W r y)) +
        psi r *
          normSq0S (I := I) (S.base.metric r) y 2 (U_tensor r y)
    HasDerivAt (fun r : Real => q r x)
        (deriv (fun r : Real => q r x) clock.time) clock.time ∧
      deriv (fun r : Real => q r x) clock.time -
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (q clock.time) x =
        hamiltonBlockJ
            (fun i j k l => S.base.rm04 clock.time x
              (vec4 (I := I) (basis i) (basis j) (basis l) (basis k)))
            (fun i j k => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (basis i) (basis j) (basis k)))
            (fun i j => hamiltonMOriginField (I := I) clock.origin clock.time
              (S.base.metric clock.time) x
                (vec2 (I := I) (basis i) (basis j)))
            (fun i j => U_tensor clock.time x
              (vec2 (I := I) (basis i) (basis j)))
            (fun i => W clock.time x (fun _ : Fin 1 => basis i)) +
          hamiltonBlockSigmaSquare
            (fun i j k l => S.base.rm04 clock.time x
              (vec4 (I := I) (basis i) (basis j) (basis l) (basis k)))
            (fun i j k => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (basis i) (basis j) (basis k)))
            (fun i j => U_tensor clock.time x
              (vec2 (I := I) (basis i) (basis j)))
            (fun i => W clock.time x (fun _ : Fin 1 => basis i)) +
          ((a' * h x - a clock.time *
                laplacianAt (I := I) (flowG (I := I) S) clock.time h x) /
              clock.elapsed + a clock.time * h x / clock.elapsed ^ 2) *
            (∑ i : Fin n,
              (W clock.time x (fun _ : Fin 1 => basis i)) ^ 2) +
          psi' * (∑ i : Fin n, ∑ j : Fin n,
            (U_tensor clock.time x
              (vec2 (I := I) (basis i) (basis j))) ^ 2) -
          2 * psi clock.time *
            (∑ e : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              (hamiltonTestJetDU clock
                (fun p q => metricRicci (I := I) (M := M)
                  (S.base.metric clock.time) x
                    (vec2 (I := I) (basis p) (basis q)))
                (fun p q => if p = q then (1 : Real) else 0)
                (fun p => W clock.time x (fun _ : Fin 1 => basis p))
                e i j) ^ 2) := by
  classical
  dsimp only
  let qBase := fun r y =>
    inner0S (I := I) (S.base.metric r) y 4
        (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
          (S.base.rm04 r) y)
        ((U_tensor r y).product (U_tensor r y)) +
      2 * inner0S (I := I) (S.base.metric r) y 3
        (hamiltonPField (I := I) (S.base.metric r) y)
        ((U_tensor r y).product (W r y)) +
      inner0S (I := I) (S.base.metric r) y 2
        (hamiltonMOriginField (I := I) clock.origin r
          (S.base.metric r) y)
        ((W r y).product (W r y))
  let FW := fun r y =>
    normSq0S (I := I) (S.base.metric r) y 1 (W r y)
  let FU := fun r y =>
    normSq0S (I := I) (S.base.metric r) y 2 (U_tensor r y)
  let c : Real → Real := a / fun r : Real => r - clock.origin
  let qW := fun r y => c r * (h y * FW r y)
  let qU := fun r y => psi r * FU r y
  let q := fun r y => qBase r y + qW r y + qU r y
  have hUskew (X Y : TangentSpace I x) :
      U_tensor clock.time x ![X, Y] =
        -U_tensor clock.time x ![Y, X] := by
    rw [← hU_tensor clock.time x]
    have hswap := (U clock.time x).map_swap (v := ![Y, X])
      (i := (0 : Fin 2)) (j := 1) (by decide)
    have hv : ![Y, X] ∘ Equiv.swap (0 : Fin 2) 1 = ![X, Y] := by
      funext q
      fin_cases q <;> simp
    rw [hv] at hswap
    exact hswap
  obtain ⟨hBaseTime, hBaseHeat⟩ :=
    hamilton_harnack_block_exact_evolution_of_tensor_test_jet
      (I := I) S hS clock ht x basis horth U_tensor W hUskew hDW hDU
        hUtime hWtime
  obtain ⟨dW, hFWTime, hFWHeat⟩ :=
    hamiltonTestW_normSq_evolution
      (I := I) S hS clock ht x basis horth W hWtime hDW
  obtain ⟨dU, hFUTime, hFUHeat⟩ :=
    hamiltonTestU_normSq_evolution
      (I := I) S hS clock ht x basis horth U_tensor hUtime
  have hcRaw := ha.div
    ((hasDerivAt_id clock.time).sub_const clock.origin)
    (sub_ne_zero.mpr (ne_of_gt clock.origin_lt_time))
  have hc : HasDerivAt c
      (a' / clock.elapsed - a clock.time / clock.elapsed ^ 2) clock.time := by
    apply (show HasDerivAt c
        ((a' * (clock.time - clock.origin) - a clock.time) /
          (clock.time - clock.origin) ^ 2) clock.time by
      simpa only [c, id_eq, mul_one] using hcRaw).congr_deriv
    simp only [HarnackClock.elapsed]
    field_simp [sub_ne_zero.mpr (ne_of_gt clock.origin_lt_time)]
  have hFWSmooth : ContMDiff I 𝓘(Real, Real) ∞ (FW clock.time) := by
    simpa only [FW, flowG] using
      normSq0S_smooth (I := I) (S.base.metric clock.time) (W clock.time)
  have hFUSmooth : ContMDiff I 𝓘(Real, Real) ∞ (FU clock.time) := by
    simpa only [FU, flowG] using
      normSq0S_smooth (I := I) (S.base.metric clock.time) (U_tensor clock.time)
  have hWCross : (S.base.metric clock.time).inner x
      (gradientFun (I := I) (S.base.metric clock.time) h x)
      (gradientFun (I := I) (S.base.metric clock.time) (FW clock.time) x) = 0 := by
    rw [show gradientFun (I := I) (S.base.metric clock.time)
        (FW clock.time) x = 0 by
      simpa only [FW] using
        hamiltonTestW_normSq_gradient_eq_zero (I := I) S clock x W hDW]
    simp
  obtain ⟨hQWTime, hQWHeat⟩ :=
    scalar_time_space_product_evolution
      (I := I) (G := flowG (I := I) S) c h FW
      (a' / clock.elapsed - a clock.time / clock.elapsed ^ 2) dW
      ((2 / clock.elapsed) * FW clock.time x)
      hc hFWTime hh hFWSmooth hWCross hFWHeat
  have hOneSmooth : ContMDiff I 𝓘(Real, Real) ∞ (fun _ : M => (1 : Real)) :=
    contMDiff_const
  have hUCross : (S.base.metric clock.time).inner x
      (gradientFun (I := I) (S.base.metric clock.time)
        (fun _ : M => (1 : Real)) x)
      (gradientFun (I := I) (S.base.metric clock.time) (FU clock.time) x) = 0 := by
    rw [gradientFun_const]
    simp
  obtain ⟨hQUTimeRaw, _⟩ :=
    scalar_time_space_product_evolution
      (I := I) (G := flowG (I := I) S) psi (fun _ : M => (1 : Real)) FU
      psi' dU
      (-2 * ∑ e : Fin n,
        inner0S (I := I) (S.base.metric clock.time) x 2
          (tensor0SCurry (I := I) (M := M) 2 x
            (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
            (basis e))
          (tensor0SCurry (I := I) (M := M) 2 x
            (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
            (basis e)))
      hpsi hFUTime hOneSmooth hFUSmooth hUCross hFUHeat
  have hQUTerm : (fun r : Real => psi r * ((1 : Real) * FU r x)) =
      fun r : Real => qU r x := by
    funext r
    simp [qU]
  have hQUTime : HasDerivAt (fun r : Real => qU r x)
      (psi' * FU clock.time x + psi clock.time * dU) clock.time := by
    rw [← hQUTerm]
    simpa using hQUTimeRaw
  have hLapURaw := laplacianAt_smul (I := I) (flowG (I := I) S)
    clock.time (psi clock.time)
    (hFUSmooth.mdifferentiable (by simp))
    (gradientFun_mdiffAt (I := I) (S.base.metric clock.time) hFUSmooth x)
  have hLapU : laplacianAt (I := I) (flowG (I := I) S) clock.time
      (qU clock.time) x =
        psi clock.time * laplacianAt (I := I) (flowG (I := I) S)
          clock.time (FU clock.time) x := by
    change laplacianAt (I := I) (flowG (I := I) S) clock.time
      ((psi clock.time) • FU clock.time) x = _
    exact hLapURaw
  have hQUHeat :
      (psi' * FU clock.time x + psi clock.time * dU) -
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (qU clock.time) x =
        psi' * FU clock.time x -
          2 * psi clock.time * ∑ e : Fin n,
            inner0S (I := I) (S.base.metric clock.time) x 2
              (tensor0SCurry (I := I) (M := M) 2 x
                (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
                (basis e))
              (tensor0SCurry (I := I) (M := M) 2 x
                (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
                (basis e)) := by
    have hFUHeat' : dU -
        laplacianAt (I := I) (flowG (I := I) S) clock.time
          (FU clock.time) x =
        -2 * ∑ e : Fin n,
          inner0S (I := I) (S.base.metric clock.time) x 2
            (tensor0SCurry (I := I) (M := M) 2 x
              (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
              (basis e))
            (tensor0SCurry (I := I) (M := M) 2 x
              (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
              (basis e)) := by
      simpa only [FU, flowG] using hFUHeat
    rw [hLapU]
    linear_combination psi clock.time * hFUHeat'
  have hQWTerm :
      (fun r : Real => c r * (h x * FW r x)) = fun r : Real => qW r x := rfl
  have hQWTime' : HasDerivAt (fun r : Real => qW r x)
      ((a' / clock.elapsed - a clock.time / clock.elapsed ^ 2) *
          (h x * FW clock.time x) +
        c clock.time * (h x * dW)) clock.time := by
    rw [← hQWTerm]
    exact hQWTime
  have hQWHeat' :
      ((a' / clock.elapsed - a clock.time / clock.elapsed ^ 2) *
          (h x * FW clock.time x) + c clock.time * (h x * dW)) -
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (qW clock.time) x =
        ((a' * h x - a clock.time *
              laplacianAt (I := I) (flowG (I := I) S) clock.time h x) /
            clock.elapsed + a clock.time * h x / clock.elapsed ^ 2) *
          FW clock.time x := by
    change ((a' / clock.elapsed - a clock.time / clock.elapsed ^ 2) *
        (h x * FW clock.time x) + c clock.time * (h x * dW)) -
        laplacianAt (I := I) (flowG (I := I) S) clock.time
          (qW clock.time) x = _ at hQWHeat
    have hcValue : c clock.time = a clock.time / clock.elapsed := by
      simp only [c, Pi.div_apply, HarnackClock.elapsed]
    rw [hcValue] at hQWHeat
    rw [hcValue]
    rw [hQWHeat]
    field_simp [clock.elapsed_ne_zero]
    ring
  have hBaseSmooth : ContMDiff I 𝓘(Real, Real) ∞ (qBase clock.time) := by
    have hK : ContMDiff I 𝓘(Real, Real) ∞
        (hamiltonKTestScalar (I := I) S U_tensor clock.time) := by
      change ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
        inner0S (I := I) (S.base.metric clock.time) y 4
          (hamiltonKField (I := I) S clock.time y)
          ((U_tensor clock.time y).product (U_tensor clock.time y)))
      simpa only [Nat.reduceAdd] using
        (inner0S_product_contMDiff (I := I) (S.base.metric clock.time)
          (hamiltonKField (I := I) S clock.time)
          (U_tensor clock.time) (U_tensor clock.time))
    have hP : ContMDiff I 𝓘(Real, Real) ∞
        (hamiltonPTestScalar (I := I) S U_tensor W clock.time) := by
      change ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
        inner0S (I := I) (S.base.metric clock.time) y 3
          (hamiltonPField (I := I) (S.base.metric clock.time) y)
          ((U_tensor clock.time y).product (W clock.time y)))
      simpa only [Nat.reduceAdd] using
        (inner0S_product_contMDiff (I := I) (S.base.metric clock.time)
          (hamiltonPField (I := I) (S.base.metric clock.time))
          (U_tensor clock.time) (W clock.time))
    have hM : ContMDiff I 𝓘(Real, Real) ∞
        (hamiltonMTestScalar (I := I) S clock W clock.time) := by
      change ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
        inner0S (I := I) (S.base.metric clock.time) y 2
          (hamiltonMOriginField (I := I) clock.origin clock.time
            (S.base.metric clock.time) y)
          ((W clock.time y).product (W clock.time y)))
      simpa only [Nat.reduceAdd] using
        (inner0S_product_contMDiff (I := I) (S.base.metric clock.time)
          (hamiltonMOriginField (I := I) clock.origin clock.time
            (S.base.metric clock.time))
          (W clock.time) (W clock.time))
    change ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      hamiltonKTestScalar (I := I) S U_tensor clock.time y +
        2 * hamiltonPTestScalar (I := I) S U_tensor W clock.time y +
        hamiltonMTestScalar (I := I) S clock W clock.time y)
    exact (hK.add (contMDiff_const.mul hP)).add hM
  have hQWSmooth : ContMDiff I 𝓘(Real, Real) ∞ (qW clock.time) := by
    exact contMDiff_const.mul (hh.mul hFWSmooth)
  have hQUSmooth : ContMDiff I 𝓘(Real, Real) ∞ (qU clock.time) := by
    exact contMDiff_const.mul hFUSmooth
  have hBaseQWSmooth : ContMDiff I 𝓘(Real, Real) ∞
      (fun y : M => qBase clock.time y + qW clock.time y) :=
    hBaseSmooth.add hQWSmooth
  have hLapBaseQW := laplacianAt_add (I := I) (flowG (I := I) S) clock.time
    (hBaseSmooth.mdifferentiable (by simp))
    (hQWSmooth.mdifferentiable (by simp))
    (gradientFun_mdiffAt (I := I) (S.base.metric clock.time) hBaseSmooth x)
    (gradientFun_mdiffAt (I := I) (S.base.metric clock.time) hQWSmooth x)
  have hLapQ := laplacianAt_add (I := I) (flowG (I := I) S) clock.time
    (hBaseQWSmooth.mdifferentiable (by simp))
    (hQUSmooth.mdifferentiable (by simp))
    (gradientFun_mdiffAt (I := I) (S.base.metric clock.time) hBaseQWSmooth x)
    (gradientFun_mdiffAt (I := I) (S.base.metric clock.time) hQUSmooth x)
  have hLap : laplacianAt (I := I) (flowG (I := I) S) clock.time
      (q clock.time) x =
        laplacianAt (I := I) (flowG (I := I) S) clock.time
            (qBase clock.time) x +
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (qW clock.time) x +
          laplacianAt (I := I) (flowG (I := I) S) clock.time
            (qU clock.time) x := by
    rw [show q clock.time = fun y : M =>
      (qBase clock.time y + qW clock.time y) + qU clock.time y by rfl,
      hLapQ]
    rw [hLapBaseQW]
  have hTimeRaw := (hBaseTime.add hQWTime').add hQUTime
  change HasDerivAt (fun r : Real => q r x) _ clock.time at hTimeRaw
  have hTime : HasDerivAt (fun r : Real => q r x)
      (deriv (fun r : Real => q r x) clock.time) clock.time := by
    exact hTimeRaw.congr_deriv hTimeRaw.deriv.symm
  have hCombined : deriv (fun r : Real => q r x) clock.time -
      laplacianAt (I := I) (flowG (I := I) S) clock.time
        (q clock.time) x =
      (hamiltonBlockJ
          (fun i j k l => S.base.rm04 clock.time x
            (vec4 (I := I) (basis i) (basis j) (basis l) (basis k)))
          (fun i j k => hamiltonPField (I := I)
            (S.base.metric clock.time) x
              (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun i j => hamiltonMOriginField (I := I) clock.origin clock.time
            (S.base.metric clock.time) x
              (vec2 (I := I) (basis i) (basis j)))
          (fun i j => U_tensor clock.time x
            (vec2 (I := I) (basis i) (basis j)))
          (fun i => W clock.time x (fun _ : Fin 1 => basis i)) +
        hamiltonBlockSigmaSquare
          (fun i j k l => S.base.rm04 clock.time x
            (vec4 (I := I) (basis i) (basis j) (basis l) (basis k)))
          (fun i j k => hamiltonPField (I := I)
            (S.base.metric clock.time) x
              (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun i j => U_tensor clock.time x
            (vec2 (I := I) (basis i) (basis j)))
          (fun i => W clock.time x (fun _ : Fin 1 => basis i))) +
        ((a' * h x - a clock.time *
              laplacianAt (I := I) (flowG (I := I) S) clock.time h x) /
            clock.elapsed + a clock.time * h x / clock.elapsed ^ 2) *
          FW clock.time x +
        psi' * FU clock.time x -
        2 * psi clock.time * ∑ e : Fin n,
          inner0S (I := I) (S.base.metric clock.time) x 2
            (tensor0SCurry (I := I) (M := M) 2 x
              (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
              (basis e))
            (tensor0SCurry (I := I) (M := M) 2 x
              (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
              (basis e)) := by
    rw [hTimeRaw.deriv, hLap]
    linear_combination hBaseHeat + hQWHeat' + hQUHeat
  let Ric : Fin n → Fin n → Real := fun p q =>
    metricRicci (I := I) (M := M) (S.base.metric clock.time) x
      (vec2 (I := I) (basis p) (basis q))
  let Wc : Fin n → Real := fun p =>
    W clock.time x (fun _ : Fin 1 => basis p)
  have hDUcomp (e i j : Fin n) :
      hamiltonTestUNablaField (I := I) S clock.time U_tensor x
          (vec3 (I := I) (basis e) (basis i) (basis j)) =
        hamiltonTestJetDU clock Ric
          (fun p q => if p = q then (1 : Real) else 0) Wc e i j := by
    change totalNabla0SFun (I := I) (M := M) 2
        (metricCov (I := I) (M := M) (S.base.metric clock.time))
        (U_tensor clock.time) x
          (vec3 (I := I) (basis e) (basis i) (basis j)) = _
    have hslots : vec3 (I := I) (basis e) (basis i) (basis j) =
        ![basis e, basis i, basis j] := by
      funext p
      fin_cases p <;> rfl
    rw [hslots, hDU]
    simp only [hamiltonTestJetDU, Ric, Wc, horth]
    have hslotsEI : vec2 (I := I) (basis e) (basis i) =
        ![basis e, basis i] := by
      funext p
      fin_cases p <;> rfl
    have hslotsEJ : vec2 (I := I) (basis e) (basis j) =
        ![basis e, basis j] := by
      funext p
      fin_cases p <;> rfl
    rw [← hslotsEI, ← hslotsEJ]
  have hWCoord : FW clock.time x = ∑ i : Fin n, (Wc i) ^ 2 := by
    simpa only [FW, Wc] using
      normSq0S_one_eq_sum_orthonormal
        (I := I) (S.base.metric clock.time) basis horth (W clock.time x)
  have hUCoord : FU clock.time x = ∑ i : Fin n, ∑ j : Fin n,
      (U_tensor clock.time x
        (vec2 (I := I) (basis i) (basis j))) ^ 2 := by
    simpa only [FU] using
      normSq0S_two_eq_sum_orthonormal
        (I := I) (S.base.metric clock.time) basis horth
          (U_tensor clock.time x)
  have hDUCoord :
      (∑ e : Fin n,
        inner0S (I := I) (S.base.metric clock.time) x 2
          (tensor0SCurry (I := I) (M := M) 2 x
            (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
            (basis e))
          (tensor0SCurry (I := I) (M := M) 2 x
            (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
            (basis e))) =
        ∑ e : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          (hamiltonTestJetDU clock Ric
            (fun p q => if p = q then (1 : Real) else 0) Wc e i j) ^ 2 := by
    exact sum_inner0S_curry_three_eq_sum_sq_orthonormal
      (I := I) (S.base.metric clock.time) basis horth
      (hamiltonTestUNablaField (I := I) S clock.time U_tensor x)
      (hamiltonTestJetDU clock Ric
        (fun p q => if p = q then (1 : Real) else 0) Wc) hDUcomp
  refine ⟨?_, ?_⟩
  · exact hTime
  · rw [show (fun r : Real =>
        inner0S (I := I) (S.base.metric r) x 4
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
              (S.base.rm04 r) x)
            ((U_tensor r x).product (U_tensor r x)) +
          2 * inner0S (I := I) (S.base.metric r) x 3
            (hamiltonPField (I := I) (S.base.metric r) x)
            ((U_tensor r x).product (W r x)) +
          inner0S (I := I) (S.base.metric r) x 2
            (hamiltonMOriginField (I := I) clock.origin r
              (S.base.metric r) x)
            ((W r x).product (W r x)) +
          a r / (r - clock.origin) * (h x *
            normSq0S (I := I) (S.base.metric r) x 1 (W r x)) +
          psi r * normSq0S (I := I) (S.base.metric r) x 2
            (U_tensor r x)) = fun r : Real => q r x by rfl]
    rw [show (fun y : M =>
        inner0S (I := I) (S.base.metric clock.time) y 4
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
              (S.base.rm04 clock.time) y)
            ((U_tensor clock.time y).product (U_tensor clock.time y)) +
          2 * inner0S (I := I) (S.base.metric clock.time) y 3
            (hamiltonPField (I := I) (S.base.metric clock.time) y)
            ((U_tensor clock.time y).product (W clock.time y)) +
          inner0S (I := I) (S.base.metric clock.time) y 2
            (hamiltonMOriginField (I := I) clock.origin clock.time
              (S.base.metric clock.time) y)
            ((W clock.time y).product (W clock.time y)) +
          a clock.time / (clock.time - clock.origin) * (h y *
            normSq0S (I := I) (S.base.metric clock.time) y 1
              (W clock.time y)) +
          psi clock.time * normSq0S (I := I) (S.base.metric clock.time) y 2
            (U_tensor clock.time y)) = q clock.time by rfl]
    rw [hCombined, hWCoord, hUCoord, hDUCoord]

omit [SigmaCompactSpace M] in
private theorem hamilton_perturbed_harnack_block_exact_evolution
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (x : M) {n : Nat}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
    (W₀ : StrongDual Real (TangentSpace I x))
    (a psi : Real → Real) (h : M → Real) (a' psi' : Real)
    (ha : HasDerivAt a a' clock.time)
    (hpsi : HasDerivAt psi psi' clock.time)
    (hh : ContMDiff I 𝓘(Real, Real) ∞ h) :
    ∃ (U : ∀ (_ : Real) (y : M),
        HamiltonHarnackTwoForm (TangentSpace I y))
      (U_tensor : Real →
        Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
      (W : Real →
        Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1),
      (∀ r y, (U r y).toTensor0S = U_tensor r y) ∧
      ContMDiff (I.prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Tensor0SModel 2 Real E)) ∞
        (fun p : M × Real =>
          (⟨p.1, U_tensor p.2 p.1⟩ :
            Bundle.TotalSpace (Tensor0SModel 2 Real E)
              (fun y : M => Tensor0SSpace 2 I y))) ∧
      ContMDiff (I.prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Tensor0SModel 1 Real E)) ∞
        (fun p : M × Real =>
          (⟨p.1, W p.2 p.1⟩ :
            Bundle.TotalSpace (Tensor0SModel 1 Real E)
              (fun y : M => Tensor0SSpace 1 I y))) ∧
      U clock.time x = U₀ ∧
      (∀ Z : TangentSpace I x,
        W clock.time x (fun _ : Fin 1 => Z) = W₀ Z) ∧
      let q := fun r y =>
        inner0S (I := I) (S.base.metric r) y 4
            (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
              (S.base.rm04 r) y)
            ((U_tensor r y).product (U_tensor r y)) +
          2 * inner0S (I := I) (S.base.metric r) y 3
            (hamiltonPField (I := I) (S.base.metric r) y)
            ((U_tensor r y).product (W r y)) +
          inner0S (I := I) (S.base.metric r) y 2
            (hamiltonMOriginField (I := I) clock.origin r
              (S.base.metric r) y)
            ((W r y).product (W r y)) +
          (a r / (r - clock.origin)) *
            (h y * normSq0S (I := I) (S.base.metric r) y 1 (W r y)) +
          psi r *
            normSq0S (I := I) (S.base.metric r) y 2 (U_tensor r y)
      HasDerivAt (fun r : Real => q r x)
          (deriv (fun r : Real => q r x) clock.time) clock.time ∧
        deriv (fun r : Real => q r x) clock.time -
            laplacianAt (I := I) (flowG (I := I) S) clock.time
              (q clock.time) x =
          hamiltonBlockJ
              (fun i j k l => S.base.rm04 clock.time x
                (vec4 (I := I) (basis i) (basis j) (basis l) (basis k)))
              (fun i j k => hamiltonPField (I := I)
                (S.base.metric clock.time) x
                  (vec3 (I := I) (basis i) (basis j) (basis k)))
              (fun i j => hamiltonMOriginField (I := I)
                clock.origin clock.time (S.base.metric clock.time) x
                  (vec2 (I := I) (basis i) (basis j)))
              (fun i j => U₀ ![basis i, basis j])
              (fun i => W₀ (basis i)) +
            hamiltonBlockSigmaSquare
              (fun i j k l => S.base.rm04 clock.time x
                (vec4 (I := I) (basis i) (basis j) (basis l) (basis k)))
              (fun i j k => hamiltonPField (I := I)
                (S.base.metric clock.time) x
                  (vec3 (I := I) (basis i) (basis j) (basis k)))
              (fun i j => U₀ ![basis i, basis j])
              (fun i => W₀ (basis i)) +
            ((a' * h x - a clock.time *
                  laplacianAt (I := I) (flowG (I := I) S) clock.time h x) /
                clock.elapsed + a clock.time * h x / clock.elapsed ^ 2) *
              (∑ i : Fin n, (W₀ (basis i)) ^ 2) +
            psi' * (∑ i : Fin n, ∑ j : Fin n,
              (U₀ ![basis i, basis j]) ^ 2) -
            2 * psi clock.time *
              (∑ e : Fin n, ∑ i : Fin n, ∑ j : Fin n,
                (hamiltonTestJetDU clock
                  (fun p q => metricRicci (I := I) (M := M)
                    (S.base.metric clock.time) x
                      (vec2 (I := I) (basis p) (basis q)))
                  (fun p q => if p = q then (1 : Real) else 0)
                  (fun p => W₀ (basis p)) e i j) ^ 2) := by
  classical
  have hmc : IsMetricCompatible (I := I)
      (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (S.base.metric clock.time) := by
    simpa [metricCov] using
      leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) (S.base.metric clock.time)
  obtain ⟨U, U_tensor, W, hU_tensor, hUjoint, hWjoint, hUvalue, hWvalue,
      hDW, hDU, hUtime, hWtime⟩ :=
    hamilton_test_jet_realization
      (I := I)
      (metricCov (I := I) (M := M) (S.base.metric clock.time))
      (metricCov_smooth (I := I) (M := M) (S.base.metric clock.time))
      (S.base.metric clock.time) hmc x clock
      (metricRicci (I := I) (M := M) (S.base.metric clock.time) x) U₀ W₀
  have hDU' : ∀ X Y Z : TangentSpace I x,
      totalNabla0SFun (I := I) (M := M) 2
          (metricCov (I := I) (M := M) (S.base.metric clock.time))
          (U_tensor clock.time) x ![X, Y, Z] =
        (1 / 2 : Real) *
            (metricRicci (I := I) (M := M) (S.base.metric clock.time) x
                ![X, Y] * W clock.time x (fun _ : Fin 1 => Z) -
              metricRicci (I := I) (M := M) (S.base.metric clock.time) x
                ![X, Z] * W clock.time x (fun _ : Fin 1 => Y)) +
          (1 / (4 * clock.elapsed) : Real) *
            ((S.base.metric clock.time).inner x X Y *
                W clock.time x (fun _ : Fin 1 => Z) -
              (S.base.metric clock.time).inner x X Z *
                W clock.time x (fun _ : Fin 1 => Y)) := by
    intro X Y Z
    simpa only [hWvalue] using hDU X Y Z
  have hexact := hamilton_perturbed_harnack_block_exact_evolution_of_test_jet
    (I := I) S hS clock ht x basis horth U U_tensor W hU_tensor hDW hDU'
      hUtime hWtime a psi h a' psi' ha hpsi hh
  have hUcomp (i j : Fin n) :
      U_tensor clock.time x (vec2 (I := I) (basis i) (basis j)) =
        U₀ ![basis i, basis j] := by
    rw [← hU_tensor clock.time x, hUvalue]
    simp only [HamiltonHarnackTwoForm.toTensor0S_apply]
    congr 1
    funext k
    fin_cases k <;> rfl
  refine ⟨U, U_tensor, W, hU_tensor, hUjoint, hWjoint, hUvalue, hWvalue, ?_⟩
  simpa only [hUcomp, hWvalue] using hexact

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem exists_contMDiff_eqOn_nhd_of_contMDiffOn
    (f : M → Real) (U : Set M) (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(Real, Real) ∞ f U) (x : M) (hx : x ∈ U) :
    ∃ f' : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ f' ∧ ∀ᶠ y in nhds x, f' y = f y := by
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (hU.mem_nhds hx)
  let f' : M → Real := fun y => χ y * f y
  have hf' : ContMDiff I 𝓘(Real, Real) ∞ f' := by
    apply contMDiff_of_tsupport
    intro y hy
    have hyχ : y ∈ tsupport (fun z : M => χ z) :=
      tsupport_mul_subset_left hy
    have hyU : y ∈ U := hχ hyχ
    exact χ.contMDiffAt.mul
      ((hf y hyU).contMDiffAt (hU.mem_nhds hyU))
  refine ⟨f', hf', ?_⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  change (χ : M → Real) y = 1 at hy
  simp only [f', hy, one_mul]

omit [FiniteDimensional Real E] in
private def tensor0SOneFormToStrongDual {x : M}
    (W : Tensor0SSpace 1 I x) : StrongDual Real (TangentSpace I x) :=
  (continuousMultilinearCurryFin0 Real (TangentSpace I x) Real).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (W.curryMid 0)

omit [FiniteDimensional Real E] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space M] in
private theorem tensor0SOneFormToStrongDual_apply {x : M}
    (W : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    tensor0SOneFormToStrongDual (I := I) W X =
      W (fun _ : Fin 1 => X) := by
  change W (Fin.insertNth 0 X 0) = W (fun _ : Fin 1 => X)
  congr 1
  funext i
  fin_cases i
  rfl

omit [SigmaCompactSpace M] in
private theorem hamilton_perturbed_test_scalar_contMDiff
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (origin r : Real)
    (U : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (W : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (a psi : Real) (h : M → Real)
    (hh : ContMDiff I 𝓘(Real, Real) ∞ h) :
    ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      inner0S (I := I) (S.base.metric r) y 4
          (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
            (S.base.rm04 r) y)
          ((U y).product (U y)) +
        2 * inner0S (I := I) (S.base.metric r) y 3
          (hamiltonPField (I := I) (S.base.metric r) y)
          ((U y).product (W y)) +
        inner0S (I := I) (S.base.metric r) y 2
          (hamiltonMOriginField (I := I) origin r
            (S.base.metric r) y)
          ((W y).product (W y)) +
        a / (r - origin) *
          (h y * normSq0S (I := I) (S.base.metric r) y 1 (W y)) +
        psi * normSq0S (I := I) (S.base.metric r) y 2 (U y)) := by
  have hK : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      inner0S (I := I) (S.base.metric r) y 4
        (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
          (S.base.rm04 r) y)
        ((U y).product (U y))) := by
    simpa only [Nat.reduceAdd] using
      (inner0S_product_contMDiff (I := I) (S.base.metric r)
        (Tensor0SField.domDomCongr ∞ curvatureSlotSwap (S.base.rm04 r)) U U)
  have hP : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      inner0S (I := I) (S.base.metric r) y 3
        (hamiltonPField (I := I) (S.base.metric r) y)
        ((U y).product (W y))) := by
    simpa only [Nat.reduceAdd] using
      (inner0S_product_contMDiff (I := I) (S.base.metric r)
        (hamiltonPField (I := I) (S.base.metric r)) U W)
  have hM : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      inner0S (I := I) (S.base.metric r) y 2
        (hamiltonMOriginField (I := I) origin r (S.base.metric r) y)
        ((W y).product (W y))) := by
    simpa only [Nat.reduceAdd] using
      (inner0S_product_contMDiff (I := I) (S.base.metric r)
        (hamiltonMOriginField (I := I) origin r (S.base.metric r)) W W)
  have hW : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      normSq0S (I := I) (S.base.metric r) y 1 (W y)) :=
    normSq0S_smooth (I := I) (S.base.metric r) W
  have hU : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M =>
      normSq0S (I := I) (S.base.metric r) y 2 (U y)) :=
    normSq0S_smooth (I := I) (S.base.metric r) U
  exact (((hK.add (contMDiff_const.mul hP)).add hM).add
    (contMDiff_const.mul (hh.mul hW))).add (contMDiff_const.mul hU)

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem tensor0S_family_eventually_ne_zero
    {s : Nat} (t : Real) (x : M)
    (A : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ s)
    (hAjoint : ContMDiff (I.prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Tensor0SModel s Real E)) ∞
      (fun p : M × Real ↦
        (⟨p.1, A p.2 p.1⟩ :
          Bundle.TotalSpace (Tensor0SModel s Real E)
            (fun y : M ↦ Tensor0SSpace s I y))))
    (hne : A t x ≠ 0) :
    ∀ᶠ p in nhds (t, x), A p.1 p.2 ≠ 0 := by
  have hswap : Continuous (fun p : Real × M ↦ (p.2, p.1)) :=
    continuous_snd.prodMk continuous_fst
  have htotal : Continuous (fun p : Real × M ↦
      (Bundle.TotalSpace.mk' (Tensor0SModel s Real E) p.2
        (A p.1 p.2) :
          Bundle.TotalSpace (Tensor0SModel s Real E)
            (fun y : M ↦ Tensor0SSpace s I y))) :=
    hAjoint.continuous.comp hswap
  have hzero : Continuous (fun p : Real × M ↦
      Bundle.zeroSection (Tensor0SModel s Real E)
        (fun y : M ↦ Tensor0SSpace s I y) p.2) :=
    (continuous_zeroSection Real
      (F := Tensor0SModel s Real E)
      (E := fun y : M ↦ Tensor0SSpace s I y)).comp continuous_snd
  have hpoint :
      (Bundle.TotalSpace.mk' (Tensor0SModel s Real E) x (A t x) :
          Bundle.TotalSpace (Tensor0SModel s Real E)
            (fun y : M ↦ Tensor0SSpace s I y)) ≠
        Bundle.zeroSection (Tensor0SModel s Real E)
          (fun y : M ↦ Tensor0SSpace s I y) x := by
    intro hzeroEq
    apply hne
    exact Bundle.TotalSpace.mk_inj.mp hzeroEq
  have hnear : ∀ᶠ p in nhds (t, x),
      (Bundle.TotalSpace.mk' (Tensor0SModel s Real E) p.2 (A p.1 p.2) :
          Bundle.TotalSpace (Tensor0SModel s Real E)
            (fun y : M ↦ Tensor0SSpace s I y)) ≠
        Bundle.zeroSection (Tensor0SModel s Real E)
          (fun y : M ↦ Tensor0SSpace s I y) p.2 :=
    (htotal.continuousAt.ne_iff_eventually_ne hzero.continuousAt).mp hpoint
  filter_upwards [hnear] with p hp
  intro hpzero
  apply hp
  rw [hpzero]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] in
private theorem hamilton_test_carrier_eventually_ne_zero
    (t : Real) (x : M)
    (U : ∀ (_ : Real) (y : M),
      HamiltonHarnackTwoForm (TangentSpace I y))
    (U_tensor : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 2)
    (W : Real →
      Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ 1)
    (hU_tensor : ∀ r y, (U r y).toTensor0S = U_tensor r y)
    (hUjoint : ContMDiff (I.prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Tensor0SModel 2 Real E)) ∞
      (fun p : M × Real ↦
        (⟨p.1, U_tensor p.2 p.1⟩ :
          Bundle.TotalSpace (Tensor0SModel 2 Real E)
            (fun y : M ↦ Tensor0SSpace 2 I y))))
    (hWjoint : ContMDiff (I.prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Tensor0SModel 1 Real E)) ∞
      (fun p : M × Real ↦
        (⟨p.1, W p.2 p.1⟩ :
          Bundle.TotalSpace (Tensor0SModel 1 Real E)
            (fun y : M ↦ Tensor0SSpace 1 I y))))
    (hne : (U t x, W t x) ≠ 0) :
    ∀ᶠ p in nhds (t, x), (U p.1 p.2, W p.1 p.2) ≠ 0 := by
  by_cases hUzero : U t x = 0
  · have hWne : W t x ≠ 0 := by
      intro hWzero
      apply hne
      exact Prod.ext hUzero hWzero
    have hnear := tensor0S_family_eventually_ne_zero
      (I := I) t x W hWjoint hWne
    filter_upwards [hnear] with p hp
    intro hzero
    exact hp (congrArg Prod.snd hzero)
  · have hUTensorNe : U_tensor t x ≠ 0 := by
      rw [← hU_tensor t x]
      exact harnackTwoForm_toTensor0S_ne_zero (I := I) hUzero
    have hnear := tensor0S_family_eventually_ne_zero
      (I := I) t x U_tensor hUjoint hUTensorNe
    filter_upwards [hnear] with p hp
    intro hzero
    apply hp
    have hUzeroAt : U p.1 p.2 = 0 := congrArg Prod.fst hzero
    rw [← hU_tensor p.1 p.2, hUzeroAt]
    exact map_zero _

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonTensor0SOfSkewComponents_skew
    {A : Type*} [Fintype A] {x : M}
    (basis : Module.Basis A Real (TangentSpace I x))
    (c : A -> A -> Real) :
    let U := hamiltonTensor0SOfComponents (I := I) basis
      (fun slots : Fin 2 -> A =>
        (c (slots 0) (slots 1) - c (slots 1) (slots 0)) / 2)
    forall X Y : TangentSpace I x, U ![X, Y] = -U ![Y, X] := by
  dsimp only
  let U := hamiltonTensor0SOfComponents (I := I) basis
    (fun slots : Fin 2 -> A =>
      (c (slots 0) (slots 1) - c (slots 1) (slots 0)) / 2)
  have htensor : U.domDomCongr (Equiv.swap (0 : Fin 2) 1) = -U := by
    apply (tensor0SBasis (I := I) basis 2).repr.injective
    ext slots
    rw [tensor0SBasis_repr, tensor0SBasis_repr]
    rw [component0S_apply]
    change U ((fun i => basis (slots i)) ∘ (Equiv.swap (0 : Fin 2) 1)) =
      (-U) (fun i => basis (slots i))
    have hswap : ((fun i => basis (slots i)) ∘ (Equiv.swap (0 : Fin 2) 1)) =
        fun i => basis (![slots 1, slots 0] i) := by
      funext i
      fin_cases i <;> rfl
    rw [hswap, hamiltonTensor0SOfComponents_apply]
    change _ = -U (fun i => basis (slots i))
    rw [hamiltonTensor0SOfComponents_apply]
    simp
    ring
  intro X Y
  have h := congrArg (fun T : Tensor0SSpace 2 I x => T ![Y, X]) htensor
  have hswapXY : ![Y, X] ∘ (Equiv.swap (0 : Fin 2) 1) = ![X, Y] := by
    funext i
    fin_cases i <;> rfl
  change U (![Y, X] ∘ (Equiv.swap (0 : Fin 2) 1)) = (-U) ![Y, X] at h
  rw [hswapXY] at h
  simpa using h

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonTwoFormOfComponents
    {A : Type*} [Fintype A] {x : M}
    (basis : Module.Basis A Real (TangentSpace I x))
    (c : A -> A -> Real) : HamiltonHarnackTwoForm (TangentSpace I x) :=
  HamiltonHarnackTwoForm.ofTensor0S (I := I)
    (hamiltonTensor0SOfComponents (I := I) basis
      (fun slots : Fin 2 -> A =>
        (c (slots 0) (slots 1) - c (slots 1) (slots 0)) / 2))
    (hamiltonTensor0SOfSkewComponents_skew (I := I) basis c)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonTwoFormOfComponents_apply
    {A : Type*} [Fintype A] {x : M}
    (basis : Module.Basis A Real (TangentSpace I x))
    (c : A -> A -> Real) (a b : A) :
    hamiltonTwoFormOfComponents (I := I) basis c ![basis a, basis b] =
      (c a b - c b a) / 2 := by
  change (hamiltonTwoFormOfComponents (I := I) basis c).toTensor0S
      ![basis a, basis b] = _
  rw [hamiltonTwoFormOfComponents,
    HamiltonHarnackTwoForm.toTensor0S_ofTensor0S]
  have h := hamiltonTensor0SOfComponents_apply (I := I) basis
    (fun slots : Fin 2 -> A =>
      (c (slots 0) (slots 1) - c (slots 1) (slots 0)) / 2) ![a, b]
  calc
    (hamiltonTensor0SOfComponents (I := I) basis
      (fun slots : Fin 2 -> A =>
        (c (slots 0) (slots 1) - c (slots 1) (slots 0)) / 2))
        ![basis a, basis b] =
      (hamiltonTensor0SOfComponents (I := I) basis
        (fun slots : Fin 2 -> A =>
          (c (slots 0) (slots 1) - c (slots 1) (slots 0)) / 2))
        (fun i => basis (![a, b] i)) := by
          congr 1
          funext i
          fin_cases i <;> rfl
    _ = (c a b - c b a) / 2 := by simpa using h

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonTensor0SOfCovectorComponents_apply
    {A : Type*} [Fintype A] {x : M}
    (basis : Module.Basis A Real (TangentSpace I x))
    (c : A -> Real) (a : A) :
    hamiltonTensor0SOfComponents (I := I) basis
        (fun slots : Fin 1 -> A => c (slots 0)) ![basis a] = c a := by
  have h := hamiltonTensor0SOfComponents_apply (I := I) basis
    (fun slots : Fin 1 -> A => c (slots 0)) ![a]
  calc
    hamiltonTensor0SOfComponents (I := I) basis
        (fun slots : Fin 1 -> A => c (slots 0)) ![basis a] =
      hamiltonTensor0SOfComponents (I := I) basis
        (fun slots : Fin 1 -> A => c (slots 0))
          (fun i => basis (![a] i)) := by
            congr 1
            funext i
            fin_cases i
            rfl
    _ = c a := by simpa using h

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamilton_sum_mul_skew_projection
    {A : Type*} [Fintype A]
    (F U : A -> A -> Real)
    (hF : forall a b, F a b = -F b a) :
    (∑ a, ∑ b, F a b * U a b) =
      ∑ a, ∑ b, F a b * ((U a b - U b a) / 2) := by
  classical
  have hswap : (∑ a, ∑ b, F a b * U b a) =
      -(∑ a, ∑ b, F a b * U a b) := by
    calc
      (∑ a, ∑ b, F a b * U b a) =
          ∑ b, ∑ a, F a b * U b a := by rw [Finset.sum_comm]
      _ = ∑ a, ∑ b, F b a * U a b := rfl
      _ = -(∑ a, ∑ b, F a b * U a b) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro b _
        rw [hF b a]
        ring
  have hterm (a b : A) :
      F a b * ((U a b - U b a) / 2) =
        (F a b * U a b - F a b * U b a) / 2 := by
    ring
  rw [show (∑ a, ∑ b, F a b * ((U a b - U b a) / 2)) =
      ((∑ a, ∑ b, F a b * U a b) -
        (∑ a, ∑ b, F a b * U b a)) / 2 by
    simp_rw [hterm, sub_div, Finset.sum_sub_distrib, ← Finset.sum_div]]
  rw [hswap]
  ring

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private noncomputable def hamiltonSkewProjection
    {A : Type*} (U : A -> A -> Real) : A -> A -> Real :=
  fun a b => (U a b - U b a) / 2

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamilton_sum_swap_four
    {A : Type*} [Fintype A]
    (F : A -> A -> A -> A -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
        ∑ b, ∑ a, ∑ c, ∑ d, F a b c d := by rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a, ∑ d, F a b c d := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ d, ∑ a, F a b c d := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ b, ∑ d, ∑ a, F a b c d := by rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamilton_sum_four_mul_skew_projection_first
    {A : Type*} [Fintype A]
    (F : A -> A -> A -> A -> Real)
    (U V : A -> A -> Real)
    (hF : forall a b c d, F a b c d = -F b a c d) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * U a b * V c d) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        F a b c d * hamiltonSkewProjection U a b * V c d := by
  classical
  have hcoeff : forall a b,
      (∑ c, ∑ d, F a b c d * V c d) =
        -(∑ c, ∑ d, F b a c d * V c d) := by
    intro a b
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [hF a b c d]
    ring
  have h := hamilton_sum_mul_skew_projection
    (fun a b => ∑ c, ∑ d, F a b c d * V c d) U hcoeff
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * U a b * V c d) =
        ∑ a, ∑ b, (∑ c, ∑ d, F a b c d * V c d) * U a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = ∑ a, ∑ b,
        (∑ c, ∑ d, F a b c d * V c d) * hamiltonSkewProjection U a b := h
    _ = ∑ a, ∑ b, ∑ c, ∑ d,
        F a b c d * hamiltonSkewProjection U a b * V c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamilton_sum_four_mul_skew_projection_second
    {A : Type*} [Fintype A]
    (F : A -> A -> A -> A -> Real)
    (U V : A -> A -> Real)
    (hF : forall a b c d, F a b c d = -F a b d c) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * U a b * V c d) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        F a b c d * U a b * hamiltonSkewProjection V c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * U a b * V c d) =
        ∑ c, ∑ d, ∑ a, ∑ b, F a b c d * U a b * V c d :=
      hamilton_sum_swap_four _
    _ = ∑ c, ∑ d, ∑ a, ∑ b,
        F a b c d * U a b * hamiltonSkewProjection V c d := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        hamilton_sum_four_mul_skew_projection_first
          (fun c d a b => F a b c d) V U (fun c d a b => hF a b c d)
    _ = ∑ a, ∑ b, ∑ c, ∑ d,
        F a b c d * U a b * hamiltonSkewProjection V c d :=
      (hamilton_sum_swap_four _).symm

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonBlockQuadratic_skew_projection
    {A : Type*} [Fintype A]
    (K : A -> A -> A -> A -> Real)
    (P : A -> A -> A -> Real)
    (M : A -> A -> Real)
    (U : A -> A -> Real) (W : A -> Real)
    (hKFirst : forall a b c d, K a b c d = -K b a c d)
    (hKLast : forall a b c d, K a b c d = -K a b d c)
    (hP : forall a b c, P a b c = -P b a c) :
    hamiltonBlockQuadratic K P M U W =
      hamiltonBlockQuadratic K P M (hamiltonSkewProjection U) W := by
  rw [hamiltonBlockQuadratic_eq_hamiltonQuadraticForm,
    hamiltonBlockQuadratic_eq_hamiltonQuadraticForm]
  unfold DifferentialGeometry.Analysis.Spectral.hamiltonQuadraticForm
  have hK1 := hamilton_sum_four_mul_skew_projection_first K U U hKFirst
  have hK2 := hamilton_sum_four_mul_skew_projection_second
    K (hamiltonSkewProjection U) U hKLast
  have hPcoeff : forall a b,
      (∑ c, P a b c * W c) = -(∑ c, P b a c * W c) := by
    intro a b
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [hP a b c]
    ring
  have hPsum := hamilton_sum_mul_skew_projection
    (fun a b => ∑ c, P a b c * W c) U hPcoeff
  have hPterm :
      (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) =
        ∑ a, ∑ b, ∑ c,
          P a b c * hamiltonSkewProjection U a b * W c := by
    calc
      (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) =
          ∑ a, ∑ b, (∑ c, P a b c * W c) * U a b := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = ∑ a, ∑ b,
          (∑ c, P a b c * W c) * hamiltonSkewProjection U a b := hPsum
      _ = ∑ a, ∑ b, ∑ c,
          P a b c * hamiltonSkewProjection U a b * W c := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
  rw [hK1, hK2, hPterm]

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedCurvatureBlock_coordinates_symmetries
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M) {A : Type*}
    (basis : Module.Basis A Real (TangentSpace I x)) (psi : Real) :
    let K := hamiltonPerturbedCurvatureBlock
      (fun a b c d => tensor04StandardAt (I := I) (M := M)
        (S.base.rm04 clock.time x) (basis a) (basis b) (basis d) (basis c)) psi
    (forall a b c d, K a b c d = K c d a b) ∧
    (forall a b c d, K a b c d = -K b a c d) ∧
    (forall a b c d, K a b c d = -K a b d c) := by
  dsimp only
  classical
  let R := metricAlgebraicCurvatureTensorAt
    (I := I) (M := M) (S.base.metric clock.time) x
  have hR : IsAlgCurvForm (tensor04StandardAt (I := I) (M := M)
      (R : Tensor04At (I := I) (M := M) x)) := R.2
  have hfirst : forall a b c d,
      tensor04StandardAt (I := I) (M := M) (S.base.rm04 clock.time x)
        (basis a) (basis b) (basis d) (basis c) =
      -tensor04StandardAt (I := I) (M := M) (S.base.rm04 clock.time x)
        (basis b) (basis a) (basis d) (basis c) := by
    intro a b c d
    simpa only [R, metricAlgebraicCurvatureTensorAt_coe,
      SolutionOn.family, SolutionFamily.rm04, metricRm04_apply] using
      hR.anti_first (basis a) (basis b) (basis d) (basis c)
  have hlast : forall a b c d,
      tensor04StandardAt (I := I) (M := M) (S.base.rm04 clock.time x)
        (basis a) (basis b) (basis d) (basis c) =
      -tensor04StandardAt (I := I) (M := M) (S.base.rm04 clock.time x)
        (basis a) (basis b) (basis c) (basis d) := by
    intro a b c d
    simpa only [R, metricAlgebraicCurvatureTensorAt_coe,
      SolutionOn.family, SolutionFamily.rm04, metricRm04_apply] using
      hR.anti_last (basis a) (basis b) (basis d) (basis c)
  have hpair : forall a b c d,
      tensor04StandardAt (I := I) (M := M) (S.base.rm04 clock.time x)
        (basis a) (basis b) (basis d) (basis c) =
      tensor04StandardAt (I := I) (M := M) (S.base.rm04 clock.time x)
        (basis c) (basis d) (basis b) (basis a) := by
    intro a b c d
    have hp := hR.pair_swap (basis a) (basis b) (basis d) (basis c)
    have hf := hR.anti_first (basis d) (basis c) (basis a) (basis b)
    have hl := hR.anti_last (basis c) (basis d) (basis a) (basis b)
    dsimp [R] at hp hf hl
    have hmetric :
        tensor04StandardAt (I := I) (M := M)
            (metricRm04At (I := I) (M := M) (S.base.metric clock.time) x)
            (basis a) (basis b) (basis d) (basis c) =
          tensor04StandardAt (I := I) (M := M)
            (metricRm04At (I := I) (M := M) (S.base.metric clock.time) x)
            (basis c) (basis d) (basis b) (basis a) := by
      change metricRm04At (I := I) (M := M) (S.base.metric clock.time) x
          (vec4 (I := I) (basis a) (basis b) (basis d) (basis c)) =
        metricRm04At (I := I) (M := M) (S.base.metric clock.time) x
          (vec4 (I := I) (basis c) (basis d) (basis b) (basis a))
      linarith
    simpa only [SolutionOn.family, SolutionFamily.rm04, metricRm04_apply] using hmetric
  have hpfirst : forall a b c d : A,
      hamiltonMetricCurvatureBlockPerturbation psi a b c d =
        -hamiltonMetricCurvatureBlockPerturbation psi b a c d := by
    intro a b c d
    unfold hamiltonMetricCurvatureBlockPerturbation
    ring
  have hplast : forall a b c d : A,
      hamiltonMetricCurvatureBlockPerturbation psi a b c d =
        -hamiltonMetricCurvatureBlockPerturbation psi a b d c := by
    intro a b c d
    unfold hamiltonMetricCurvatureBlockPerturbation
    ring
  have hppair : forall a b c d : A,
      hamiltonMetricCurvatureBlockPerturbation psi a b c d =
        hamiltonMetricCurvatureBlockPerturbation psi c d a b := by
    intro a b c d
    have heq (i j : A) : (if i = j then (1 : Real) else 0) =
        if j = i then 1 else 0 := by
      by_cases h : i = j
      · rw [if_pos h, if_pos h.symm]
      · have h' : j ≠ i := fun hij : j = i => h hij.symm
        rw [if_neg h, if_neg h']
    unfold hamiltonMetricCurvatureBlockPerturbation
    rw [heq c a, heq d b, heq c b, heq d a]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    unfold hamiltonPerturbedCurvatureBlock
    dsimp only
    rw [hpair, hppair]
  · intro a b c d
    unfold hamiltonPerturbedCurvatureBlock
    dsimp only
    rw [hfirst, hpfirst]
    ring
  · intro a b c d
    unfold hamiltonPerturbedCurvatureBlock
    dsimp only
    rw [hlast, hplast]
    ring

omit [SigmaCompactSpace M] in
private theorem hamiltonP_coordinates_skew
    (g : SmoothRiemannianMetric I M) (x : M)
    {A : Type*}
    (basis : Module.Basis A Real (TangentSpace I x)) :
    forall a b c,
      hamiltonPAt (I := I) g x ![basis a, basis b, basis c] =
        -hamiltonPAt (I := I) g x ![basis b, basis a, basis c] := by
  intro a b c
  have habc : ![basis a, basis b, basis c] =
      vec3 (I := I) (basis a) (basis b) (basis c) := by
    funext i
    fin_cases i <;> rfl
  have hbac : ![basis b, basis a, basis c] =
      vec3 (I := I) (basis b) (basis a) (basis c) := by
    funext i
    fin_cases i <;> rfl
  rw [habc, hbac]
  exact hamiltonPAt_skew (I := I) g x (basis a) (basis b) (basis c)

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedMBlock_coordinates_symm
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    {A : Type*}
    (basis : Module.Basis A Real (TangentSpace I x)) (phi : Real) :
    forall a b,
      hamiltonPerturbedMBlock clock
          (fun i j => hamiltonMAt (I := I) clock
            (S.base.metric clock.time) x ![basis i, basis j]) phi a b =
        hamiltonPerturbedMBlock clock
          (fun i j => hamiltonMAt (I := I) clock
            (S.base.metric clock.time) x ![basis i, basis j]) phi b a := by
  classical
  intro a b
  have hab : ![basis a, basis b] =
      vec2 (I := I) (basis a) (basis b) := by
    funext i
    fin_cases i <;> rfl
  have hba : ![basis b, basis a] =
      vec2 (I := I) (basis b) (basis a) := by
    funext i
    fin_cases i <;> rfl
  have hM := hamiltonMAt_symm (I := I) S clock ht x (basis a) (basis b)
  rw [← hab, ← hba] at hM
  change hamiltonMAt (I := I) clock (S.base.metric clock.time) x
      ![basis a, basis b] =
    hamiltonMAt (I := I) clock (S.base.metric clock.time) x
      ![basis b, basis a] at hM
  unfold hamiltonPerturbedMBlock
  dsimp only
  by_cases h : a = b
  · subst b
    rfl
  · have h' : b ≠ a := fun hba' : b = a => h hba'.symm
    rw [if_neg h, if_neg h', mul_zero, add_zero]
    simpa using hM

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedBlockPSD_of_harnack_nonneg
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (phi psi : Real) (x : M)
    {A : Type*} [Fintype A] [DecidableEq A]
    (basis : Module.Basis A Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I)
      (S.base.metric clock.time) x basis (identityInvMetric (Idx := A)))
    (hnonneg : forall
      (U : HamiltonHarnackTwoForm (TangentSpace I x))
      (W : Tensor0SSpace 1 I x),
        0 <= hamiltonPerturbedHarnackQuadraticAt
          (I := I) S clock phi psi x U W) :
    hamiltonBlockPSD
      (hamiltonPerturbedCurvatureBlock
        (fun a b c d => tensor04StandardAt (I := I) (M := M)
          (S.base.rm04 clock.time x) (basis a) (basis b) (basis d) (basis c))
        psi)
      (fun a b c => hamiltonPAt (I := I)
        (S.base.metric clock.time) x ![basis a, basis b, basis c])
      (hamiltonPerturbedMBlock clock
        (fun a b => hamiltonMAt (I := I) clock
          (S.base.metric clock.time) x ![basis a, basis b]) phi) := by
  classical
  let K := hamiltonPerturbedCurvatureBlock
    (fun a b c d => tensor04StandardAt (I := I) (M := M)
      (S.base.rm04 clock.time x) (basis a) (basis b) (basis d) (basis c)) psi
  let P := fun a b c => hamiltonPAt (I := I)
    (S.base.metric clock.time) x ![basis a, basis b, basis c]
  let Mblock := hamiltonPerturbedMBlock clock
    (fun a b => hamiltonMAt (I := I) clock
      (S.base.metric clock.time) x ![basis a, basis b]) phi
  change hamiltonBlockPSD K P Mblock
  intro U W
  have h := hnonneg
    (hamiltonTwoFormOfComponents (I := I) basis U)
    (hamiltonTensor0SOfComponents (I := I) basis
      (fun slots : Fin 1 -> A => W (slots 0)))
  rw [hamiltonPerturbedHarnackQuadraticAt_eq_block
    (I := I) S clock phi psi x
      (hamiltonTwoFormOfComponents (I := I) basis U)
      (hamiltonTensor0SOfComponents (I := I) basis
        (fun slots : Fin 1 -> A => W (slots 0))) basis hinv] at h
  have hskew : 0 <= hamiltonBlockQuadratic K P Mblock
      (fun a b => (U a b - U b a) / 2) W := by
    simpa only [K, P, Mblock,
      hamiltonTwoFormOfComponents_apply,
      hamiltonTensor0SOfCovectorComponents_apply] using h
  have hK := hamiltonPerturbedCurvatureBlock_coordinates_symmetries
    (I := I) S clock x basis psi
  have hP := hamiltonP_coordinates_skew
    (I := I) (S.base.metric clock.time) x basis
  rw [hamiltonBlockQuadratic_skew_projection K P Mblock U W
    hK.2.1 hK.2.2 hP]
  change 0 <= hamiltonBlockQuadratic K P Mblock
    (fun a b => (U a b - U b a) / 2) W
  exact hskew

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedBlockJ_nonneg_of_harnack_nonneg_of_null
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    (phi psi : Real) (x : M)
    {A : Type*} [Fintype A] [DecidableEq A]
    (basis : Module.Basis A Real (TangentSpace I x))
    (hinv : MetricInverseInBasis (I := I)
      (S.base.metric clock.time) x basis (identityInvMetric (Idx := A)))
    (hnonneg : forall
      (U : HamiltonHarnackTwoForm (TangentSpace I x))
      (W : Tensor0SSpace 1 I x),
        0 <= hamiltonPerturbedHarnackQuadraticAt
          (I := I) S clock phi psi x U W)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x)
    (hzero : hamiltonPerturbedHarnackQuadraticAt
      (I := I) S clock phi psi x U W = 0) :
    0 <= hamiltonBlockJ
      (hamiltonPerturbedCurvatureBlock
        (fun a b c d => tensor04StandardAt (I := I) (M := M)
          (S.base.rm04 clock.time x) (basis a) (basis b) (basis d) (basis c))
        psi)
      (fun a b c => hamiltonPAt (I := I)
        (S.base.metric clock.time) x ![basis a, basis b, basis c])
      (hamiltonPerturbedMBlock clock
        (fun a b => hamiltonMAt (I := I) clock
          (S.base.metric clock.time) x ![basis a, basis b]) phi)
      (fun a b => U ![basis a, basis b])
      (fun a => W ![basis a]) := by
  classical
  let K := hamiltonPerturbedCurvatureBlock
    (fun a b c d => tensor04StandardAt (I := I) (M := M)
      (S.base.rm04 clock.time x) (basis a) (basis b) (basis d) (basis c)) psi
  let P := fun a b c => hamiltonPAt (I := I)
    (S.base.metric clock.time) x ![basis a, basis b, basis c]
  let Mblock := hamiltonPerturbedMBlock clock
    (fun a b => hamiltonMAt (I := I) clock
      (S.base.metric clock.time) x ![basis a, basis b]) phi
  change 0 <= hamiltonBlockJ K P Mblock
    (fun a b => U ![basis a, basis b]) (fun a => W ![basis a])
  have hK := hamiltonPerturbedCurvatureBlock_coordinates_symmetries
    (I := I) S clock x basis psi
  have hP := hamiltonP_coordinates_skew
    (I := I) (S.base.metric clock.time) x basis
  have hM := hamiltonPerturbedMBlock_coordinates_symm
    (I := I) S clock ht x basis phi
  have hPSD := hamiltonPerturbedBlockPSD_of_harnack_nonneg
    (I := I) S clock phi psi x basis hinv hnonneg
  have hU : forall a b,
      U ![basis a, basis b] = -U ![basis b, basis a] := by
    intro a b
    calc
      U ![basis a, basis b] = U (fun i => basis (![a, b] i)) := by
        exact congrArg U (by funext i; fin_cases i <;> rfl)
      _ = -U (fun i => basis (![b, a] i)) := by
        simpa only [HamiltonHarnackTwoForm.component, component0S_apply,
          HamiltonHarnackTwoForm.toTensor0S_apply] using
            HamiltonHarnackTwoForm.component_skew (I := I) basis U a b
      _ = -U ![basis b, basis a] := by
        congr 1
        exact congrArg U (by funext i; fin_cases i <;> rfl)
  have hzeroBlock : hamiltonBlockQuadratic K P Mblock
      (fun a b => U ![basis a, basis b]) (fun a => W ![basis a]) = 0 := by
    rw [← hamiltonPerturbedHarnackQuadraticAt_eq_block
      (I := I) S clock phi psi x U W basis hinv]
    exact hzero
  exact hamiltonBlockJ_nonneg_of_psd_quadratic_eq_zero
    K P Mblock (fun a b => U ![basis a, basis b])
      (fun a => W ![basis a]) hK.1 hK.2.1 hP hM hPSD hU hzeroBlock

omit [SigmaCompactSpace M] in
theorem hamiltonBlockJ_add_sigmaSquare_nonneg_of_harnack_nonneg
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    {A : Type*} [Fintype A] [DecidableEq A]
    (basis : Module.Basis A ℝ (TangentSpace I x))
    (horth : ∀ i j, (S.base.metric clock.time).inner x (basis i) (basis j) =
      if i = j then (1 : ℝ) else 0)
    (hnonneg : ∀ (U : HamiltonHarnackTwoForm (TangentSpace I x))
      (W : Tensor0SSpace 1 I x),
      0 ≤ hamiltonHarnackQuadraticAt (I := I) S clock x U W)
    (U : A → A → ℝ) (W : A → ℝ) (hU : ∀ a b, U a b = -U b a) :
    let K := fun a b c d => tensor04StandardAt (I := I) (M := M)
      (S.base.rm04 clock.time x) (basis a) (basis b) (basis d) (basis c)
    let P := fun a b c => hamiltonPAt (I := I)
      (S.base.metric clock.time) x ![basis a, basis b, basis c]
    let Mbar := fun a b => hamiltonMAt (I := I) clock
      (S.base.metric clock.time) x ![basis a, basis b]
    0 ≤ hamiltonBlockJ K P Mbar U W + hamiltonBlockSigmaSquare K P U W := by
  dsimp only
  have hinv := metricInverseInBasis_identity_of_orthonormal
    (S.base.metric clock.time) basis horth
  have hK := hamiltonPerturbedCurvatureBlock_coordinates_symmetries
    (I := I) S clock x basis 0
  have hM := hamiltonPerturbedMBlock_coordinates_symm
    (I := I) S clock ht x basis 0
  have hPSD := hamiltonPerturbedBlockPSD_of_harnack_nonneg
    (I := I) S clock 0 0 x basis hinv (by
      simpa only [hamiltonPerturbedHarnackQuadraticAt, zero_div, zero_mul, add_zero]
        using hnonneg)
  simp only [hamiltonPerturbedCurvatureBlock, hamiltonMetricCurvatureBlockPerturbation,
    hamiltonPerturbedMBlock, zero_div, zero_mul, add_zero] at hK hM
  simp only [hamiltonBlockPSD, hamiltonBlockQuadratic, hamiltonBlockPolarized,
    hamiltonPerturbedCurvatureBlock,
    hamiltonMetricCurvatureBlockPerturbation, hamiltonPerturbedMBlock,
    zero_div, zero_mul, add_zero] at hPSD
  rw [← hamiltonBlock_exact_evolution_eq_j_add_sigma_square]
  exact hamiltonBlock_exact_evolution_nonneg_of_psd _ _ _ U W
    hK.1 hK.2.1 (hamiltonP_coordinates_skew (S.base.metric clock.time) x basis)
    hM hPSD hU

omit [SigmaCompactSpace M] in
private theorem hamilton_perturbed_harnack_exact_rhs_pos_of_null
    {D : RealTimeInterval} {n : Nat}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : M)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (K S0 B C phi Lphi psi psi' : Real)
    (hS0 : 0 ≤ S0) (helapsed : clock.elapsed ≤ S0)
    (hderiv : ∀ k : Nat, k ≤ 2 →
      nablaKRm04NormSqIntrinsic (I := I) S k clock.time x ≤ K)
    (hB : B = Real.sqrt K + (n : Real) * Real.sqrt K +
      (n : Real) * Real.sqrt K +
      S0 * ((n : Real) ^ 2 * Real.sqrt K +
        (n : Real) ^ 3 * (Real.sqrt K) ^ 2) +
      (n : Real) * Real.sqrt K / 2)
    (hCphi : 2 * (B + 1) * (n : Real) ^ 3 ≤ C)
    (hCpsiW : 2 * B * S0 * (n : Real) ^ 3 +
      4 * B * S0 ^ 2 * (n : Real) ^ 4 +
      B * S0 ^ 2 * (n : Real) ^ 2 +
      4 * B ^ 2 * S0 ^ 2 * (n : Real) ^ 2 +
      (n : Real) ^ 2 ≤ C)
    (hCpsiU : 4 * B * (n : Real) ^ 3 +
      (8 * B + 4) * (n : Real) ^ 4 + B * (n : Real) +
      2 * B * (n : Real) ^ 2 + 1 ≤ C)
    (hphi : 0 ≤ phi) (hpsi : 0 ≤ psi) (hpsi1 : psi ≤ 1)
    (hnonneg : ∀
      (U : HamiltonHarnackTwoForm (TangentSpace I x))
      (W : Tensor0SSpace 1 I x),
        0 ≤ hamiltonPerturbedHarnackQuadraticAt
          (I := I) S clock phi psi x U W)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x)
    (hzero : hamiltonPerturbedHarnackQuadraticAt
      (I := I) S clock phi psi x U W = 0)
    (hne : (U, W) ≠ 0)
    (hWcoefficient : 0 < Lphi / clock.elapsed + phi / clock.elapsed ^ 2 -
      C * psi / clock.elapsed ^ 2 - C * phi / clock.elapsed)
    (hUcoefficient : 0 < psi' - C * psi) :
    0 < hamiltonBlockJ
          (fun i j k l => S.base.rm04 clock.time x
            (vec4 (I := I) (basis i) (basis j) (basis l) (basis k)))
          (fun i j k => hamiltonPField (I := I)
            (S.base.metric clock.time) x
              (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun i j => hamiltonMOriginField (I := I)
            clock.origin clock.time (S.base.metric clock.time) x
              (vec2 (I := I) (basis i) (basis j)))
          (fun i j => U ![basis i, basis j])
          (fun i => W ![basis i]) +
        hamiltonBlockSigmaSquare
          (fun i j k l => S.base.rm04 clock.time x
            (vec4 (I := I) (basis i) (basis j) (basis l) (basis k)))
          (fun i j k => hamiltonPField (I := I)
            (S.base.metric clock.time) x
              (vec3 (I := I) (basis i) (basis j) (basis k)))
          (fun i j => U ![basis i, basis j])
          (fun i => W ![basis i]) +
        (Lphi / clock.elapsed + phi / clock.elapsed ^ 2) *
          (∑ i : Fin n, (W ![basis i]) ^ 2) +
        psi' * (∑ i : Fin n, ∑ j : Fin n,
          (U ![basis i, basis j]) ^ 2) -
        2 * psi *
          (∑ e : Fin n, ∑ i : Fin n, ∑ j : Fin n,
            (hamiltonTestJetDU clock
              (fun p q => metricRicci (I := I) (M := M)
                (S.base.metric clock.time) x
                  (vec2 (I := I) (basis p) (basis q)))
              (fun p q => if p = q then (1 : Real) else 0)
              (fun p => W ![basis p]) e i j) ^ 2) := by
  classical
  let R : Fin n → Fin n → Fin n → Fin n → Real := fun a b c d =>
    S.base.rm04 clock.time x
      (vec4 (I := I) (basis a) (basis b) (basis c) (basis d))
  let Ric : Fin n → Fin n → Real := fun a b =>
    metricRicci (I := I) (M := M) (S.base.metric clock.time) x
      (vec2 (I := I) (basis a) (basis b))
  let nablaR : Fin n → Fin n → Fin n → Fin n → Fin n → Real :=
    fun e a b c d => nablaRm04Field (I := I) S clock.time x
      (vec5 (I := I) (basis e) (basis a) (basis b) (basis c) (basis d))
  let nablaRic : Fin n → Fin n → Fin n → Real := fun a b c =>
    metricNablaRic (I := I) (M := M) (S.base.metric clock.time) x
      (vec3 (I := I) (basis a) (basis b) (basis c))
  let nablaP : Fin n → Fin n → Fin n → Fin n → Real := fun e a b c =>
    metricNabla2Ric (I := I) (M := M) (S.base.metric clock.time) x
        (vec4 (I := I) (basis e) (basis a) (basis b) (basis c)) -
      metricNabla2Ric (I := I) (M := M) (S.base.metric clock.time) x
        (vec4 (I := I) (basis e) (basis b) (basis a) (basis c))
  let Uc : Fin n → Fin n → Real := fun a b => U ![basis a, basis b]
  let Wc : Fin n → Real := fun a => W ![basis a]
  have hU : ∀ a b, Uc a b = -Uc b a := by
    intro a b
    dsimp only [Uc]
    calc
      U ![basis a, basis b] = U (fun i => basis (![a, b] i)) := by
        exact congrArg U (by funext i; fin_cases i <;> rfl)
      _ = -U (fun i => basis (![b, a] i)) := by
        simpa only [HamiltonHarnackTwoForm.component, component0S_apply,
          HamiltonHarnackTwoForm.toTensor0S_apply] using
            HamiltonHarnackTwoForm.component_skew (I := I) basis U a b
      _ = -U ![basis b, basis a] := by
        congr 1
        exact congrArg U (by funext i; fin_cases i <;> rfl)
  have hdiv : ∀ a b, (∑ e, nablaP e e a b) =
      hamiltonDivPAt (I := I) (S.base.metric clock.time) x
        (vec2 (I := I) (basis a) (basis b)) := by
    intro a b
    have hinvTrace := metricInverseInBasis_of_orthonormal
      (I := I) (S.base.metric clock.time) basis horth
    have htrace := hamiltonDivPAt_apply_eq_trace_hamiltonNablaP
      (I := I) (S.base.metric clock.time) basis
        (identityInvMetric (Idx := Fin n)) hinvTrace (basis a) (basis b)
    simp only [identityInvMetric, diagonalInvMetric, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at htrace
    symm
    simpa only [nablaP, hamiltonNablaPField_apply] using htrace
  have hMcomp : hamiltonMComponent clock R Ric
      (fun i j => ∑ e, nablaP e e i j) = fun a b =>
        hamiltonMOriginField (I := I) clock.origin clock.time
          (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b)) := by
    funext a b
    simp_rw [hdiv]
    calc
      hamiltonMComponent clock R Ric
          (fun i j => hamiltonDivPAt (I := I)
            (S.base.metric clock.time) x
              (vec2 (I := I) (basis i) (basis j))) a b =
          hamiltonMAt (I := I) clock (S.family.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b)) := by
        change hamiltonMComponent clock
            (fun i j k l => metricRm04 (I := I) (M := M)
              (S.family.metric clock.time) x
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))
            (fun i j => metricRicci (I := I) (M := M)
              (S.family.metric clock.time) x
              (vec2 (I := I) (basis i) (basis j)))
            (fun i j => hamiltonDivPAt (I := I)
              (S.family.metric clock.time) x
              (vec2 (I := I) (basis i) (basis j))) a b = _
        exact hamiltonMComponent_eq_hamiltonMAt_orthonormal
          (I := I) S hS clock ht x basis horth a b
      _ = hamiltonMAt (I := I) clock (S.base.metric clock.time) x
          (vec2 (I := I) (basis a) (basis b)) := rfl
      _ = hamiltonMOriginField (I := I) clock.origin clock.time
          (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b)) := by
        rw [← hamiltonMField_apply (I := I) S hS clock ht x]
        rfl
  have hM : ∀ a b,
      hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) a b =
        hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j) b a := by
    intro a b
    rw [hMcomp]
    change hamiltonMField (I := I) clock (S.base.metric clock.time) x
        (vec2 (I := I) (basis a) (basis b)) =
      hamiltonMField (I := I) clock (S.base.metric clock.time) x
        (vec2 (I := I) (basis b) (basis a))
    rw [hamiltonMField_apply (I := I) S hS clock ht x]
    exact hamiltonMAt_symm (I := I) S clock ht x (basis a) (basis b)
  have heq := hamiltonPerturbedBlock_heat_product_eq_j_add_sigma_square
    clock R Ric nablaR nablaRic nablaP (fun _ _ _ => 0)
      phi Lphi psi psi' Uc Wc
      (hamilton_rm_components_symm
        (I := I) S ⟨clock.time, ht⟩ x basis)
      (hamilton_nabla_rm_components_pair_symm
        (I := I) S clock.time x basis horth)
      (by
        intro a b
        exact metricRicciAt_symm (I := I) (S.base.metric clock.time) x
          (basis a) (basis b))
      (by
        intro a b c
        exact metricNablaRic_last_two_symm
          (I := I) (M := M) (S.base.metric clock.time) x
            (basis a) (basis b) (basis c))
      (hamilton_curvature_ricci_trace_components
        (I := I) S ⟨clock.time, ht⟩ x basis horth)
      (hamilton_contracted_curvature_derivative_components
        (I := I) S clock.time x basis horth)
      (by intro e a b c; dsimp only [nablaP]; ring)
      hM hU
  have hreaction := hamiltonPerturbedBlock_reaction_ge_of_curvature_derivative_bound
    (I := I) S hS clock ht x basis horth K S0 B C
      phi Lphi psi psi' hS0 helapsed hderiv hB hCphi hCpsiW hCpsiU
      Uc Wc hU hphi hpsi hpsi1
  dsimp only at hreaction
  rw [heq] at hreaction
  have hPcomp : hamiltonPComponent nablaRic = fun a b c =>
      hamiltonPField (I := I) (S.base.metric clock.time) x
        (vec3 (I := I) (basis a) (basis b) (basis c)) := by
    funext a b c
    simp only [nablaRic, hamiltonPComponent, hamiltonPField_apply,
      hamiltonPAt_apply]
  rw [hPcomp, hMcomp] at hreaction
  have hinv : MetricInverseInBasis (I := I)
      (S.base.metric clock.time) x basis
      (identityInvMetric (Idx := Fin n)) :=
    metricInverseInBasis_of_orthonormal (I := I)
      (S.base.metric clock.time) basis horth
  have hJ := hamiltonPerturbedBlockJ_nonneg_of_harnack_nonneg_of_null
    (I := I) S clock ht phi psi x basis hinv hnonneg U W hzero
  have hPAtcomp :
      (fun a b c => hamiltonPAt (I := I)
        (S.base.metric clock.time) x ![basis a, basis b, basis c]) =
        fun a b c => hamiltonPAt (I := I)
          (S.base.metric clock.time) x
            (vec3 (I := I) (basis a) (basis b) (basis c)) := by
    funext a b c
    congr 1
    funext i
    fin_cases i <;> rfl
  have hMAtcomp :
      (fun a b => hamiltonMAt (I := I) clock
        (S.base.metric clock.time) x ![basis a, basis b]) =
        fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
          (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b)) := by
    funext a b
    calc
      hamiltonMAt (I := I) clock (S.base.metric clock.time) x
          ![basis a, basis b] =
          hamiltonMAt (I := I) clock (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b)) := by
        congr 1
        funext i
        fin_cases i <;> rfl
      _ = hamiltonMField (I := I) clock (S.base.metric clock.time) x
          (vec2 (I := I) (basis a) (basis b)) := by
        rw [hamiltonMField_apply (I := I) S hS clock ht x]
      _ = hamiltonMOriginField (I := I) clock.origin clock.time
          (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b)) := rfl
  have hJ' : 0 ≤ hamiltonBlockJ
      (hamiltonPerturbedCurvatureBlock
        (fun a b c d => S.base.rm04 clock.time x
          (vec4 (I := I) (basis a) (basis b) (basis d) (basis c))) psi)
      (fun a b c => hamiltonPField (I := I)
        (S.base.metric clock.time) x
          (vec3 (I := I) (basis a) (basis b) (basis c)))
      (hamiltonPerturbedMBlock clock
        (fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
          (S.base.metric clock.time) x
            (vec2 (I := I) (basis a) (basis b))) phi) Uc Wc := by
    rw [hPAtcomp, hMAtcomp] at hJ
    simpa only [Uc, Wc, tensor04StandardAt_apply, hamiltonPField_apply] using hJ
  have hSigma : 0 ≤ hamiltonBlockSigmaSquare
      (hamiltonPerturbedCurvatureBlock
        (fun a b c d => S.base.rm04 clock.time x
          (vec4 (I := I) (basis a) (basis b) (basis d) (basis c))) psi)
      (fun a b c => hamiltonPField (I := I)
        (S.base.metric clock.time) x
          (vec3 (I := I) (basis a) (basis b) (basis c))) Uc Wc := by
    unfold hamiltonBlockSigmaSquare
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  let W2 := ∑ i : Fin n, (Wc i) ^ 2
  let U2 := ∑ i : Fin n, ∑ j : Fin n, (Uc i j) ^ 2
  have hW2 : 0 ≤ W2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU2 : 0 ≤ U2 := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcarrier : 0 <
      (Lphi / clock.elapsed + phi / clock.elapsed ^ 2 -
          C * psi / clock.elapsed ^ 2 - C * phi / clock.elapsed) * W2 +
        (psi' - C * psi) * U2 := by
    by_cases hUz : U = 0
    · have hWz : W ≠ 0 := by
        intro hW
        apply hne
        simp only [hUz, hW, Prod.zero_eq_mk]
      have hWnorm : normSq0S (I := I) (S.base.metric clock.time) x 1 W = W2 := by
        calc
          normSq0S (I := I) (S.base.metric clock.time) x 1 W =
              ∑ a : Fin n, (W (fun _ : Fin 1 => basis a)) ^ 2 :=
            normSq0S_one_eq_sum_orthonormal
              (I := I) (S.base.metric clock.time) basis horth W
          _ = W2 := by
            dsimp only [W2, Wc]
            apply Finset.sum_congr rfl
            intro a _
            rw [show (fun _ : Fin 1 => basis a) = ![basis a] by
              funext i
              fin_cases i
              rfl]
      have hW2pos : 0 < W2 := by
        rw [← hWnorm]
        exact (tensor0SMetricData (I := I) (S.base.metric clock.time) x 1).inner_pos_of_ne_zero
          hWz
      exact add_pos_of_pos_of_nonneg (mul_pos hWcoefficient hW2pos)
        (mul_nonneg hUcoefficient.le hU2)
    · have hUtensor : U.toTensor0S ≠ 0 :=
        harnackTwoForm_toTensor0S_ne_zero (I := I) hUz
      have hUnorm : normSq0S (I := I) (S.base.metric clock.time) x 2
          U.toTensor0S = U2 := by
        calc
          normSq0S (I := I) (S.base.metric clock.time) x 2 U.toTensor0S =
              ∑ a : Fin n, ∑ b : Fin n,
                (U.toTensor0S (vec2 (I := I) (basis a) (basis b))) ^ 2 :=
            normSq0S_two_eq_sum_orthonormal
              (I := I) (S.base.metric clock.time) basis horth U.toTensor0S
          _ = U2 := by
            dsimp only [U2, Uc]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            simp only [HamiltonHarnackTwoForm.toTensor0S_apply]
            rw [show vec2 (I := I) (basis a) (basis b) =
                ![basis a, basis b] by
              funext i
              fin_cases i <;> rfl]
      have hU2pos : 0 < U2 := by
        rw [← hUnorm]
        exact (tensor0SMetricData (I := I) (S.base.metric clock.time) x 2).inner_pos_of_ne_zero
          hUtensor
      exact add_pos_of_nonneg_of_pos (mul_nonneg hWcoefficient.le hW2)
        (mul_pos hUcoefficient hU2pos)
  have hlower : 0 <
      hamiltonBlockJ
          (hamiltonPerturbedCurvatureBlock
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (basis a) (basis b) (basis d) (basis c))) psi)
          (fun a b c => hamiltonPField (I := I)
            (S.base.metric clock.time) x
              (vec3 (I := I) (basis a) (basis b) (basis c)))
          (hamiltonPerturbedMBlock clock
            (fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
              (S.base.metric clock.time) x
                (vec2 (I := I) (basis a) (basis b))) phi) Uc Wc +
        hamiltonBlockSigmaSquare
          (hamiltonPerturbedCurvatureBlock
            (fun a b c d => S.base.rm04 clock.time x
              (vec4 (I := I) (basis a) (basis b) (basis d) (basis c))) psi)
          (fun a b c => hamiltonPField (I := I)
            (S.base.metric clock.time) x
              (vec3 (I := I) (basis a) (basis b) (basis c))) Uc Wc +
        (Lphi / clock.elapsed + phi / clock.elapsed ^ 2 -
          C * psi / clock.elapsed ^ 2 - C * phi / clock.elapsed) * W2 +
        (psi' - C * psi) * U2 := by
    have hnonnegative : 0 ≤
        hamiltonBlockJ
            (hamiltonPerturbedCurvatureBlock
              (fun a b c d => S.base.rm04 clock.time x
                (vec4 (I := I) (basis a) (basis b) (basis d) (basis c))) psi)
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (basis a) (basis b) (basis c)))
            (hamiltonPerturbedMBlock clock
              (fun a b => hamiltonMOriginField (I := I) clock.origin clock.time
                (S.base.metric clock.time) x
                  (vec2 (I := I) (basis a) (basis b))) phi) Uc Wc +
          hamiltonBlockSigmaSquare
            (hamiltonPerturbedCurvatureBlock
              (fun a b c d => S.base.rm04 clock.time x
                (vec4 (I := I) (basis a) (basis b) (basis d) (basis c))) psi)
            (fun a b c => hamiltonPField (I := I)
              (S.base.metric clock.time) x
                (vec3 (I := I) (basis a) (basis b) (basis c))) Uc Wc :=
      add_nonneg hJ' hSigma
    simpa only [add_assoc] using
      add_pos_of_nonneg_of_pos hnonnegative hcarrier
  apply hlower.trans_le
  simpa only [R, Ric, Uc, Wc, W2, U2] using hreaction

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamilton_weighted_two_mul_le
    {N B psi u w : Real}
    (hN : 0 < N) (hpsi : 0 < psi) :
    2 * B * u * w <=
      psi / (2 * N) * u ^ 2 + 2 * N * B ^ 2 / psi * w ^ 2 := by
  have hden : 0 < 2 * N * psi := by positivity
  have hscaled :
      (2 * N * psi) * (2 * B * u * w) <=
        (2 * N * psi) *
          (psi / (2 * N) * u ^ 2 + 2 * N * B ^ 2 / psi * w ^ 2) := by
    field_simp
    nlinarith [sq_nonneg (psi * u - 2 * N * B * w)]
  exact le_of_mul_le_mul_left hscaled hden

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamilton_mixed_term_abs_le
    {A : Type*} [Fintype A] [Nonempty A]
    (P : A -> A -> A -> Real)
    (U : A -> A -> Real) (W : A -> Real)
    (B psi : Real) (hpsi : 0 < psi)
    (hP : forall a b c, |P a b c| <= B) :
    |2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c)| <=
      psi / 2 * (∑ a, ∑ b, (U a b) ^ 2) +
        2 * B ^ 2 * (Fintype.card A : Real) ^ 3 / psi *
          (∑ c, (W c) ^ 2) := by
  classical
  let N : Real := Fintype.card A
  have hN : 0 < N := by
    dsimp only [N]
    positivity
  have hterm : forall a b c,
      2 * |P a b c * U a b * W c| <=
        psi / (2 * N) * (U a b) ^ 2 +
          2 * N * B ^ 2 / psi * (W c) ^ 2 := by
    intro a b c
    rw [abs_mul, abs_mul]
    calc
      2 * (|P a b c| * |U a b| * |W c|) =
          2 * |P a b c| * |U a b| * |W c| := by ring
      _ <= 2 * B * |U a b| * |W c| := by
        have hpu := mul_le_mul_of_nonneg_right (hP a b c) (abs_nonneg (U a b))
        have hpuw := mul_le_mul_of_nonneg_right hpu (abs_nonneg (W c))
        nlinarith
      _ <= psi / (2 * N) * |U a b| ^ 2 +
          2 * N * B ^ 2 / psi * |W c| ^ 2 :=
        hamilton_weighted_two_mul_le hN hpsi
      _ = psi / (2 * N) * (U a b) ^ 2 +
          2 * N * B ^ 2 / psi * (W c) ^ 2 := by
        simp only [sq_abs]
  have hfirst :
      (∑ a, ∑ b, ∑ _c : A, psi / (2 * N) * (U a b) ^ 2) =
        psi / 2 * (∑ a, ∑ b, (U a b) ^ 2) := by
    have hcancel (u : Real) :
        N * (psi / (2 * N) * u ^ 2) = psi / 2 * u ^ 2 := by
      field_simp [ne_of_gt hN]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [show (Fintype.card A : Real) = N by rfl, hcancel]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  have hsecond :
      (∑ _a : A, ∑ _b : A, ∑ c,
          2 * N * B ^ 2 / psi * (W c) ^ 2) =
        2 * B ^ 2 * (Fintype.card A : Real) ^ 3 / psi *
          (∑ c, (W c) ^ 2) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (Fintype.card A : Real) = N by rfl]
    rw [show (∑ c, 2 * N * B ^ 2 / psi * (W c) ^ 2) =
        (2 * N * B ^ 2 / psi) * (∑ c, (W c) ^ 2) by
      rw [Finset.mul_sum]]
    ring
  calc
    |2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c)| =
        2 * |∑ a, ∑ b, ∑ c, P a b c * U a b * W c| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    _ <= 2 * (∑ a, ∑ b, ∑ c, |P a b c * U a b * W c|) := by
      gcongr
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun a _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _))
    _ = ∑ a, ∑ b, ∑ c, 2 * |P a b c * U a b * W c| := by
      simp_rw [Finset.mul_sum]
    _ <= ∑ a, ∑ b, ∑ c,
        (psi / (2 * N) * (U a b) ^ 2 +
          2 * N * B ^ 2 / psi * (W c) ^ 2) := by
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        Finset.sum_le_sum fun c _ => hterm a b c
    _ = psi / 2 * (∑ a, ∑ b, (U a b) ^ 2) +
        2 * B ^ 2 * (Fintype.card A : Real) ^ 3 / psi *
          (∑ c, (W c) ^ 2) := by
      simp only [Finset.sum_add_distrib]
      rw [hfirst, hsecond]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonPerturbedBlockQuadratic_ge_of_unshifted_bounds
    {A : Type*} [Fintype A] [Nonempty A]
    (clock : HarnackClock)
    (K : A -> A -> A -> A -> Real)
    (P : A -> A -> A -> Real)
    (Mbar Ric : A -> A -> Real)
    (phi psi B : Real)
    (U : A -> A -> Real) (W : A -> Real)
    (hU : forall a b, U a b = -U b a)
    (hK : 0 <= ∑ a, ∑ b, ∑ c, ∑ d,
      K a b c d * U a b * U c d)
    (hRic : 0 <= ∑ a, ∑ b, Ric a b * W a * W b)
    (hB : 0 <= B) (hpsi : 0 < psi)
    (hP : forall a b c, |P a b c| <= B)
    (hMbar : forall a b, |Mbar a b| <= B) :
    hamiltonBlockQuadratic
        (hamiltonPerturbedCurvatureBlock K psi) P
        (hamiltonPerturbedMBlock clock
          (fun a b => Mbar a b +
            (1 / (2 * clock.elapsed)) * Ric a b) phi) U W >=
      psi / 2 * (∑ a, ∑ b, (U a b) ^ 2) +
        (phi / clock.elapsed -
            B * (Fintype.card A : Real) -
            2 * B ^ 2 * (Fintype.card A : Real) ^ 3 / psi) *
          (∑ a, (W a) ^ 2) := by
  let U2 := ∑ a, ∑ b, (U a b) ^ 2
  let W2 := ∑ a, (W a) ^ 2
  let mixed := 2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c)
  let mbarquad := ∑ a, ∑ b, Mbar a b * W a * W b
  let ricquad := ∑ a, ∑ b, Ric a b * W a * W b
  have hmixedAbs :
      |mixed| <= psi / 2 * U2 +
        2 * B ^ 2 * (Fintype.card A : Real) ^ 3 / psi * W2 := by
    exact hamilton_mixed_term_abs_le P U W B psi hpsi hP
  have hmixed :
      -(psi / 2 * U2 +
          2 * B ^ 2 * (Fintype.card A : Real) ^ 3 / psi * W2) <= mixed :=
    neg_le_of_abs_le hmixedAbs
  have hmbarquadAbs :
      |mbarquad| <= B * (Fintype.card A : Real) * W2 := by
    exact DifferentialGeometry.Tensor0SBundle.abs_quadratic_sum_le
      Mbar W B hB hMbar
  have hmbarquad :
      -(B * (Fintype.card A : Real) * W2) <= mbarquad :=
    neg_le_of_abs_le hmbarquadAbs
  have hshift : 0 <= (1 / (2 * clock.elapsed)) * ricquad :=
    mul_nonneg (one_div_pos.mpr (mul_pos (by norm_num) clock.elapsed_pos)).le hRic
  rw [hamiltonPerturbedBlockQuadratic_expand clock K P
    (fun a b => Mbar a b + (1 / (2 * clock.elapsed)) * Ric a b)
    phi psi U W hU]
  rw [hamiltonBlockQuadratic_eq_hamiltonQuadraticForm]
  unfold DifferentialGeometry.Analysis.Spectral.hamiltonQuadraticForm
  have hMsplit :
      (∑ a, ∑ b,
          (Mbar a b + (1 / (2 * clock.elapsed)) * Ric a b) * W a * W b) =
        mbarquad + (1 / (2 * clock.elapsed)) * ricquad := by
    dsimp only [mbarquad, ricquad]
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    ring_nf
  rw [hMsplit]
  change
    (∑ a, ∑ b, ∑ c, ∑ d, K a b c d * U a b * U c d) +
        mixed + (mbarquad + (1 / (2 * clock.elapsed)) * ricquad) +
          phi / clock.elapsed * W2 + psi * U2 >= _
  dsimp only [U2, W2, ricquad] at hK hmixed hmbarquad hshift ⊢
  ring_nf at hmixed hmbarquad hshift ⊢
  linarith

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamilton_curvature_block_coordinates_nonneg
    {x : M} {A : Type*} [Fintype A]
    (R : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hR : R ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (basis : Module.Basis A Real (TangentSpace I x))
    (U : A -> A -> Real) :
    0 <= ∑ a, ∑ b, ∑ c, ∑ d,
      tensor04StandardAt (I := I) (M := M) (R : Tensor04At (I := I) (M := M) x)
        (basis a) (basis b) (basis d) (basis c) * U a b * U c d := by
  classical
  let e : Fin (Fintype.card (A × A)) ≃ A × A := (Fintype.equivFin (A × A)).symm
  let F : (A × A) -> (A × A) -> Real := fun p q =>
    U p.1 p.2 * U q.1 q.2 *
      tensor04StandardAt (I := I) (M := M) (R : Tensor04At (I := I) (M := M) x)
        (basis p.1) (basis p.2) (basis q.2) (basis q.1)
  have h := mem_algebraicCurvatureOperatorNonnegativeCone.mp hR
    (Fintype.card (A × A))
    (fun i => U (e i).1 (e i).2)
    (fun i => basis (e i).1) (fun i => basis (e i).2)
  unfold algebraicCurvatureOperatorQuadraticEval at h
  have heq :
      (∑ i : Fin (Fintype.card (A × A)),
          ∑ j : Fin (Fintype.card (A × A)), F (e i) (e j)) =
        ∑ p : A × A, ∑ q : A × A, F p q := by
    rw [Equiv.sum_comp e (fun p => ∑ j, F p (e j))]
    apply Finset.sum_congr rfl
    intro p _
    rw [Equiv.sum_comp e (F p)]
  have hF : 0 <= ∑ p : A × A, ∑ q : A × A, F p q := by
    rw [← heq]
    simpa only [F, e, mul_assoc] using h
  rw [Fintype.sum_prod_type] at hF
  simp_rw [Fintype.sum_prod_type] at hF
  have hfinal :
      (∑ a, ∑ b, ∑ c, ∑ d,
          tensor04StandardAt (I := I) (M := M) (R : Tensor04At (I := I) (M := M) x)
            (basis a) (basis b) (basis d) (basis c) * U a b * U c d) =
        ∑ a, ∑ b, ∑ c, ∑ d,
          U a b * U c d *
            tensor04StandardAt (I := I) (M := M) (R : Tensor04At (I := I) (M := M) x)
              (basis a) (basis b) (basis d) (basis c) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hfinal]
  simpa only [F] using hF

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamilton_ricci_coordinates_nonneg
    {x : M} {A : Type*} [Fintype A]
    (R : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hR : R ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (basis : Module.Basis A Real (TangentSpace I x))
    (Ric : A -> A -> Real)
    (htrace : curvatureRicciTraceComponents
      (fun a b c d =>
        tensor04StandardAt (I := I) (M := M)
          (R : Tensor04At (I := I) (M := M) x)
          (basis a) (basis b) (basis c) (basis d)) Ric)
    (W : A -> Real) :
    0 <= ∑ a, ∑ b, Ric a b * W a * W b := by
  classical
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  have hsection : forall q : A,
      0 <= ∑ a, ∑ b,
        tensor04StandardAt (I := I) (M := M)
            (R : Tensor04At (I := I) (M := M) x)
            (basis q) (basis a) (basis b) (basis q) * W a * W b := by
    intro q
    let F : A -> A -> Real := fun a b =>
      W a * W b *
        tensor04StandardAt (I := I) (M := M)
          (R : Tensor04At (I := I) (M := M) x)
          (basis q) (basis a) (basis b) (basis q)
    have h := mem_algebraicCurvatureOperatorNonnegativeCone.mp hR
      (Fintype.card A) (fun i => W (e i))
      (fun _ => basis q) (fun i => basis (e i))
    unfold algebraicCurvatureOperatorQuadraticEval at h
    have heq :
        (∑ i : Fin (Fintype.card A), ∑ j : Fin (Fintype.card A),
            F (e i) (e j)) =
          ∑ a : A, ∑ b : A, F a b := by
      rw [Equiv.sum_comp e (fun a => ∑ j, F a (e j))]
      apply Finset.sum_congr rfl
      intro a _
      rw [Equiv.sum_comp e (F a)]
    calc
      0 <= ∑ a : A, ∑ b : A, F a b := by
        rw [← heq]
        simpa only [F, e, mul_assoc, mul_comm, mul_left_comm] using h
      _ = ∑ a, ∑ b,
          tensor04StandardAt (I := I) (M := M)
              (R : Tensor04At (I := I) (M := M) x)
              (basis q) (basis a) (basis b) (basis q) * W a * W b := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [F]
        ring
  have hsum : 0 <= ∑ q : A, ∑ a, ∑ b,
      tensor04StandardAt (I := I) (M := M)
          (R : Tensor04At (I := I) (M := M) x)
          (basis q) (basis a) (basis b) (basis q) * W a * W b :=
    Finset.sum_nonneg fun q _ => hsection q
  calc
    (∑ a, ∑ b, Ric a b * W a * W b) =
        ∑ a, ∑ b, (∑ q,
          tensor04StandardAt (I := I) (M := M)
            (R : Tensor04At (I := I) (M := M) x)
            (basis q) (basis a) (basis b) (basis q)) * W a * W b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [htrace a b]
    _ = ∑ a, ∑ b, ∑ q,
        tensor04StandardAt (I := I) (M := M)
            (R : Tensor04At (I := I) (M := M) x)
            (basis q) (basis a) (basis b) (basis q) * W a * W b := by
      simp only [Finset.sum_mul]
    _ = ∑ a, ∑ q, ∑ b,
        tensor04StandardAt (I := I) (M := M)
            (R : Tensor04At (I := I) (M := M) x)
            (basis q) (basis a) (basis b) (basis q) * W a * W b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ q, ∑ a, ∑ b,
        tensor04StandardAt (I := I) (M := M)
            (R : Tensor04At (I := I) (M := M) x)
            (basis q) (basis a) (basis b) (basis q) * W a * W b := by
      rw [Finset.sum_comm]
    _ >= 0 := hsum

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackQuadraticAt_ge_of_unshifted_coefficients
    [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (phi psi B : Real)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x)
    (basis : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x))
    (horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (hR : metricAlgebraicCurvatureTensorAt
      (I := I) (M := M) (S.base.metric clock.time) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hB : 0 <= B) (hpsi : 0 < psi)
    (hP : forall a b c,
      |hamiltonPAt (I := I) (S.base.metric clock.time) x
        ![basis a, basis b, basis c]| <= B)
    (hMbar : forall a b,
      |hamiltonMbarAt (I := I) (S.base.metric clock.time) x
        ![basis a, basis b]| <= B) :
    hamiltonPerturbedHarnackQuadraticAt (I := I) S clock phi psi x U W >=
      psi / 2 * normSq0S (I := I) (S.base.metric clock.time) x 2 U.toTensor0S +
        (phi / clock.elapsed -
            B * (Module.finrank Real E : Real) -
            2 * B ^ 2 * (Module.finrank Real E : Real) ^ 3 / psi) *
          normSq0S (I := I) (S.base.metric clock.time) x 1 W := by
  classical
  have hinv : MetricInverseInBasis (I := I)
      (S.base.metric clock.time) x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real E))) :=
    metricInverseInBasis_of_orthonormal (I := I)
      (S.base.metric clock.time) basis horth
  rw [hamiltonPerturbedHarnackQuadraticAt_eq_block
    (I := I) S clock phi psi x U W basis hinv]
  have hUskew : forall a b,
      U ![basis a, basis b] = -U ![basis b, basis a] := by
    intro a b
    calc
      U ![basis a, basis b] = U (fun i => basis (![a, b] i)) := by
        exact congrArg U (by funext i; fin_cases i <;> rfl)
      _ = -U (fun i => basis (![b, a] i)) := by
        simpa only [HamiltonHarnackTwoForm.component, component0S_apply,
          HamiltonHarnackTwoForm.toTensor0S_apply] using
            HamiltonHarnackTwoForm.component_skew (I := I) basis U a b
      _ = -U ![basis b, basis a] := by
        congr 1
        exact congrArg U (by funext i; fin_cases i <;> rfl)
  have hK := hamilton_curvature_block_coordinates_nonneg
    (I := I)
    (metricAlgebraicCurvatureTensorAt
      (I := I) (M := M) (S.base.metric clock.time) x)
    hR basis (fun a b => U ![basis a, basis b])
  have htrace : curvatureRicciTraceComponents
      (fun a b c d => tensor04StandardAt (I := I) (M := M)
        (metricAlgebraicCurvatureTensorAt
          (I := I) (M := M) (S.base.metric clock.time) x :
            Tensor04At (I := I) (M := M) x)
        (basis a) (basis b) (basis c) (basis d))
      (fun a b => metricRicci (I := I) (M := M)
        (S.base.metric clock.time) x
        (vec2 (I := I) (basis a) (basis b))) := by
    intro a b
    symm
    simpa [metricAlgebraicCurvatureTensorAt_coe, metricRm04_apply,
      SolutionOn.family, SolutionFamily.rm04,
      SolutionOn.ricci, SolutionFamily.ricci] using
      (ricci_diag_eq_sum_rm04_diag_of_orthonormal
        (I := I) (S.base.metric clock.time) basis
        (S.ricci clock.time) (S.base.rm13 clock.time) (S.base.rm04 clock.time)
        (ricciTraceOfSolution (I := I) S clock.time)
        (solution_rm04LowersRm13At (I := I) S clock.time x) horth a b)
  have hRic := hamilton_ricci_coordinates_nonneg
    (I := I)
    (metricAlgebraicCurvatureTensorAt
      (I := I) (M := M) (S.base.metric clock.time) x)
    hR basis
    (fun a b => metricRicci (I := I) (M := M)
      (S.base.metric clock.time) x
      (vec2 (I := I) (basis a) (basis b))) htrace
    (fun a => W ![basis a])
  have hMform :
      (fun a b => hamiltonMAt (I := I) clock
        (S.base.metric clock.time) x ![basis a, basis b]) =
        fun a b =>
          hamiltonMbarAt (I := I) (S.base.metric clock.time) x
              ![basis a, basis b] +
            (1 / (2 * clock.elapsed)) *
              metricRicci (I := I) (M := M) (S.base.metric clock.time) x
                (vec2 (I := I) (basis a) (basis b)) := by
    funext a b
    have hslots : ![basis a, basis b] =
        vec2 (I := I) (basis a) (basis b) := by
      funext i
      fin_cases i <;> rfl
    rw [hslots]
    simp only [hamiltonMAt, Tensor0SSpace.add_apply,
      Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [hMform]
  have hbound := hamiltonPerturbedBlockQuadratic_ge_of_unshifted_bounds clock
    (fun a b c d => tensor04StandardAt (I := I) (M := M)
      (S.base.rm04 clock.time x) (basis a) (basis b) (basis d) (basis c))
    (fun a b c => hamiltonPAt (I := I)
      (S.base.metric clock.time) x ![basis a, basis b, basis c])
    (fun a b => hamiltonMbarAt (I := I) (S.base.metric clock.time) x
      ![basis a, basis b])
    (fun a b => metricRicci (I := I) (M := M)
      (S.base.metric clock.time) x
      (vec2 (I := I) (basis a) (basis b)))
    phi psi B (fun a b => U ![basis a, basis b])
    (fun a => W ![basis a]) hUskew (by
      simpa only [metricAlgebraicCurvatureTensorAt_coe,
        SolutionOn.family, SolutionFamily.rm04, metricRm04_apply] using hK)
    hRic hB hpsi hP hMbar
  have hUnorm :
      normSq0S (I := I) (S.base.metric clock.time) x 2 U.toTensor0S =
        ∑ a, ∑ b, (U ![basis a, basis b]) ^ 2 := by
    rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq
      (I := I) (S.base.metric clock.time) x 2 basis hinv U.toTensor0S]
    rw [Tensor0SBundle.sum_fin_two_fun]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [component0S_apply, HamiltonHarnackTwoForm.toTensor0S_apply]
    congr 1
    exact congrArg U (by funext i; fin_cases i <;> rfl)
  have hWnorm :
      normSq0S (I := I) (S.base.metric clock.time) x 1 W =
        ∑ a, (W ![basis a]) ^ 2 := by
    rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq
      (I := I) (S.base.metric clock.time) x 1 basis hinv W]
    rw [Tensor0SBundle.sum_fin_one_fun]
    apply Finset.sum_congr rfl
    intro a _
    simp only [component0S_apply]
    congr 1
    exact congrArg W (by funext i; fin_cases i; rfl)
  rw [hUnorm, hWnorm]
  simpa only [Fintype.card_fin] using hbound

private theorem exists_hamiltonPerturbedHarnackQuadratic_slab_lower_bound
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alpha beta stop C : Real}
    (halphaBeta : alpha < beta)
    (hbetaStop : beta <= stop)
    (hslab : Set.Icc alpha stop ⊆ D.carrier)
    (hreg : Set.Ioc alpha stop ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric alpha))
    (hC : 0 <= C)
    (hcurv : forall t, t ∈ Set.Icc alpha stop -> forall x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) <= C)
    (hR : forall t, t ∈ Set.Icc beta stop -> forall x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    exists B : Real, 0 <= B ∧
      forall (clock : HarnackClock), clock.time ∈ Set.Icc beta stop ->
      forall (x : M), forall phi psi : Real, 0 < psi ->
      forall U : HamiltonHarnackTwoForm (TangentSpace I x),
      forall W : Tensor0SSpace 1 I x,
      hamiltonPerturbedHarnackQuadraticAt (I := I) S clock phi psi x U W >=
        psi / 2 * normSq0S (I := I) (S.base.metric clock.time) x 2 U.toTensor0S +
          (phi / clock.elapsed -
              B * (Module.finrank Real E : Real) -
              2 * B ^ 2 * (Module.finrank Real E : Real) ^ 3 / psi) *
            normSq0S (I := I) (S.base.metric clock.time) x 1 W := by
  obtain ⟨B, hB, hcoeff⟩ := hamilton_unshifted_coefficients_bound_on_slab
    (I := I) S hS halphaBeta hbetaStop hslab hreg hcomplete hC hcurv
  refine ⟨B, hB, ?_⟩
  intro clock htime x phi psi hpsi U W
  obtain ⟨basis0, horth0⟩ := exists_orthonormal_basis
    (I := I) (S.base.metric clock.time) x
  have hdim : Module.finrank Real (TangentSpace I x) = Module.finrank Real E := rfl
  let basis : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) :=
    basis0.reindex (finCongr hdim)
  have horth : forall i j,
      (S.base.metric clock.time).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    simp only [basis, Module.Basis.reindex_apply]
    rw [horth0]
    simp
  have hbounds := hcoeff clock.time htime x basis horth
  apply hamiltonPerturbedHarnackQuadraticAt_ge_of_unshifted_coefficients
    (I := I) S clock x phi psi B U W basis horth (hR clock.time htime x)
      hB hpsi
  · intro a b c
    have hslots : ![basis a, basis b, basis c] =
        vec3 (I := I) (basis a) (basis b) (basis c) := by
      funext i
      fin_cases i <;> rfl
    rw [hslots, hamiltonPAt, hamiltonP_apply]
    exact hbounds.1 a b c
  · intro a b
    have hslots : ![basis a, basis b] =
        vec2 (I := I) (basis a) (basis b) := by
      funext i
      fin_cases i <;> rfl
    rw [hslots]
    exact hbounds.2 a b

private def hamiltonBarrierPhi
    (epsilon A origin : Real) (h : M -> Real) (t : Real) (x : M) : Real :=
  epsilon * Real.exp (A * (t - origin)) * h x

private def hamiltonBarrierPsi
    (kappa epsilon B origin t : Real) : Real :=
  kappa * epsilon * Real.exp (B * (t - origin))

private theorem exists_hamilton_barrier_parameters
    {C Ch S : Real} (hC : 0 <= C) (hCh : 0 <= Ch) :
    exists A B kappa : Real,
      0 < kappa ∧ C < A - Ch ∧ C < B ∧
        forall s, s ∈ Set.Icc (0 : Real) S ->
          C * kappa * Real.exp ((B - A) * s) < 1 := by
  let A := C + Ch + 1
  let B := A + 1
  let kappa := (2 * (C + 1) * Real.exp S)⁻¹
  have hC1 : 0 < C + 1 := by linarith
  have hden : 0 < 2 * (C + 1) * Real.exp S := by positivity
  refine ⟨A, B, kappa, inv_pos.mpr hden, ?_, ?_, ?_⟩
  · dsimp only [A]
    linarith
  · dsimp only [B, A]
    linarith
  · intro s hs
    have hexp : Real.exp s <= Real.exp S := Real.exp_le_exp.mpr hs.2
    have hfactor : 0 <= C * kappa := mul_nonneg hC (inv_pos.mpr hden).le
    calc
      C * kappa * Real.exp ((B - A) * s) =
          C * kappa * Real.exp s := by
            congr 2
            dsimp only [B]
            ring
      _ <= C * kappa * Real.exp S :=
        mul_le_mul_of_nonneg_left hexp hfactor
      _ = C / (2 * (C + 1)) := by
        dsimp only [kappa]
        field_simp [Real.exp_ne_zero]
      _ < 1 := by
        rw [div_lt_one (by positivity : 0 < 2 * (C + 1))]
        linarith

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [TopologicalSpace M] in
private theorem hamilton_barrier_phi_gt_control_mul_psi
    {C A B kappa epsilon origin stop t h : Real} {x : M}
    (hclock : origin <= t) (htstop : t <= stop)
    (hepsilon : 0 < epsilon) (hh : 1 <= h)
    (hsmall : forall s, s ∈ Set.Icc (0 : Real) (stop - origin) ->
      C * kappa * Real.exp ((B - A) * s) < 1) :
    C * hamiltonBarrierPsi kappa epsilon B origin t <
      hamiltonBarrierPhi (M := M) epsilon A origin (fun _ => h) t x := by
  have htau : t - origin ∈ Set.Icc (0 : Real) (stop - origin) := by
    constructor <;> linarith
  have hfactor : 0 < epsilon * Real.exp (A * (t - origin)) := by
    positivity
  have hstrict : C * kappa * Real.exp ((B - A) * (t - origin)) < h :=
    (hsmall (t - origin) htau).trans_le hh
  have hexp : Real.exp (B * (t - origin)) =
      Real.exp (A * (t - origin)) *
        Real.exp ((B - A) * (t - origin)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold hamiltonBarrierPsi hamiltonBarrierPhi
  rw [hexp]
  nlinarith

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamilton_barrier_psi_derivative_gt_control_mul_psi
    {C B kappa epsilon origin t : Real}
    (hCB : C < B) (hkappa : 0 < kappa) (hepsilon : 0 < epsilon) :
    C * hamiltonBarrierPsi kappa epsilon B origin t <
      B * hamiltonBarrierPsi kappa epsilon B origin t := by
  have hpsi : 0 < hamiltonBarrierPsi kappa epsilon B origin t := by
    unfold hamiltonBarrierPsi
    positivity
  exact mul_lt_mul_of_pos_right hCB hpsi

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamilton_barrier_supported_phi_heat_gt_control_mul_phi
    {C Ch A epsilon origin t h lap : Real}
    (hCA : C < A - Ch) (hepsilon : 0 < epsilon)
    (hh : 1 <= h) (hlap : lap <= Ch * h) :
    C * (epsilon * Real.exp (A * (t - origin)) * h) <
      A * (epsilon * Real.exp (A * (t - origin)) * h) -
        epsilon * Real.exp (A * (t - origin)) * lap := by
  let factor := epsilon * Real.exp (A * (t - origin))
  have hfactor : 0 < factor := by
    dsimp only [factor]
    positivity
  have hphi : 0 < factor * h :=
    mul_pos hfactor (lt_of_lt_of_le zero_lt_one hh)
  have hlapScaled : factor * lap <= Ch * (factor * h) := by
    calc
      factor * lap <= factor * (Ch * h) :=
        mul_le_mul_of_nonneg_left hlap hfactor.le
      _ = Ch * (factor * h) := by ring
  dsimp only [factor] at hphi hlapScaled ⊢
  nlinarith

private theorem exists_hamiltonPerturbedHarnackQuadraticValue_strict_support
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {origin stop reactionK S0 reactionB reactionC Ch barrierA barrierB
      kappa epsilon t : Real}
    (ht : t ∈ Set.Ioc origin stop)
    (hreg : Set.Ioc origin stop ⊆ D.regular)
    (hS0 : 0 ≤ S0) (helapsed : t - origin ≤ S0)
    (hderiv : ∀ k : Nat, k ≤ 2 → ∀ x : M,
      nablaKRm04NormSqIntrinsic (I := I) S k t x ≤ reactionK)
    (hReactionB : reactionB = Real.sqrt reactionK +
      (Module.finrank Real E : Real) * Real.sqrt reactionK +
      (Module.finrank Real E : Real) * Real.sqrt reactionK +
      S0 * ((Module.finrank Real E : Real) ^ 2 * Real.sqrt reactionK +
        (Module.finrank Real E : Real) ^ 3 * (Real.sqrt reactionK) ^ 2) +
      (Module.finrank Real E : Real) * Real.sqrt reactionK / 2)
    (hReactionCphi : 2 * (reactionB + 1) *
      (Module.finrank Real E : Real) ^ 3 ≤ reactionC)
    (hReactionCpsiW :
      2 * reactionB * S0 * (Module.finrank Real E : Real) ^ 3 +
        4 * reactionB * S0 ^ 2 * (Module.finrank Real E : Real) ^ 4 +
        reactionB * S0 ^ 2 * (Module.finrank Real E : Real) ^ 2 +
        4 * reactionB ^ 2 * S0 ^ 2 *
          (Module.finrank Real E : Real) ^ 2 +
        (Module.finrank Real E : Real) ^ 2 ≤ reactionC)
    (hReactionCpsiU :
      4 * reactionB * (Module.finrank Real E : Real) ^ 3 +
        (8 * reactionB + 4) * (Module.finrank Real E : Real) ^ 4 +
        reactionB * (Module.finrank Real E : Real) +
        2 * reactionB * (Module.finrank Real E : Real) ^ 2 + 1 ≤ reactionC)
    (hCA : reactionC < barrierA - Ch) (hCB : reactionC < barrierB)
    (hkappa : 0 < kappa) (hepsilon : 0 < epsilon)
    (hsmall : ∀ s, s ∈ Set.Icc (0 : Real) (stop - origin) →
      reactionC * kappa * Real.exp ((barrierB - barrierA) * s) < 1)
    (hpsi1 : hamiltonBarrierPsi kappa epsilon barrierB origin t ≤ 1)
    (h : M → Real) (hh : ∀ y, 1 ≤ h y)
    (x : M) {U : Set M} (hU : IsOpen U) (hxU : x ∈ U)
    (hbar : M → Real)
    (hbarSmooth : ContMDiffOn I 𝓘(Real, Real) ∞ hbar U)
    (hbarEq : hbar x = h x)
    (hbarUpper : ∀ᶠ y in nhds x, h y ≤ hbar y)
    (hbarLap : laplacian (I := I)
      (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t) hbar x ≤
        Ch * h x)
    (hnonnegative : ∀ y z,
      0 ≤ hamiltonPerturbedHarnackQuadraticValue
        (E := E) (I := I) (M := M) S origin
        (hamiltonBarrierPhi epsilon barrierA origin h)
        (hamiltonBarrierPsi kappa epsilon barrierB origin) t y z)
    (z : HarnackCarrierFiber (E := E) (I := I) (M := M) x)
    (hnull : hamiltonPerturbedHarnackQuadraticValue
      (E := E) (I := I) (M := M) S origin
      (hamiltonBarrierPhi epsilon barrierA origin h)
      (hamiltonBarrierPsi kappa epsilon barrierB origin) t x z = 0) :
    ∃ (extension : Real → ∀ y,
        HarnackCarrierFiber (E := E) (I := I) (M := M) y)
      (f : Real → M → Real) (timeDeriv : Real),
      extension t x = z ∧
      f t x = hamiltonPerturbedHarnackQuadraticValue
        (E := E) (I := I) (M := M) S origin
        (hamiltonBarrierPhi epsilon barrierA origin h)
        (hamiltonBarrierPsi kappa epsilon barrierB origin)
          t x (extension t x) ∧
      (∀ᶠ p in nhdsWithin (t, x) (Set.Ioc origin stop ×ˢ Set.univ),
        hamiltonPerturbedHarnackQuadraticValue
          (E := E) (I := I) (M := M) S origin
          (hamiltonBarrierPhi epsilon barrierA origin h)
          (hamiltonBarrierPsi kappa epsilon barrierB origin)
            p.1 p.2 (extension p.1 p.2) ≤ f p.1 p.2) ∧
      HasDerivWithinAt (fun s : Real ↦ f s x) timeDeriv
        (Set.Ioc origin stop) t ∧
      MDifferentiableAt I 𝓘(Real, Real) (f t) x ∧
      (∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) (f t) y) ∧
      MDiffAt (T% fun y : M ↦
        gradientFun (I := I) (S.base.metric t) (f t) y) x ∧
      0 < timeDeriv - laplacian (I := I)
        (LeviCivita (I := I) (S.base.metric t))
          (S.base.metric t) (f t) x := by
  classical
  let _ := ‹SigmaCompactSpace M›
  let clock : HarnackClock := ⟨origin, t, ht.1⟩
  obtain ⟨basis0, horth0⟩ :=
    exists_orthonormal_basis (I := I) (S.base.metric t) x
  have hdim : Module.finrank Real (TangentSpace I x) =
      Module.finrank Real E := rfl
  let basis : Module.Basis (Fin (Module.finrank Real E)) Real
      (TangentSpace I x) := basis0.reindex (finCongr hdim)
  have horth : ∀ i j,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    simp only [basis, Module.Basis.reindex_apply]
    rw [horth0]
    simp
  obtain ⟨htilde, htildeSmooth, htildeEq⟩ :=
    exists_contMDiff_eqOn_nhd_of_contMDiffOn
      (I := I) hbar U hU hbarSmooth x hxU
  have htildeEqX : htilde x = hbar x := htildeEq.self_of_nhds
  have hUpper : ∀ᶠ y in nhds x, h y ≤ htilde y := by
    filter_upwards [hbarUpper, htildeEq] with y hy hyEq
    rwa [hyEq]
  let a : Real → Real := fun r ↦
    epsilon * Real.exp (barrierA * (r - origin))
  let psi : Real → Real := fun r ↦
    kappa * epsilon * Real.exp (barrierB * (r - origin))
  have ha : HasDerivAt a (barrierA * a t) t := by
    have hraw : HasDerivAt a
        (epsilon * (Real.exp (barrierA * (t - origin)) * barrierA)) t := by
      simpa only [a, id_eq, mul_one] using
        (((((hasDerivAt_id t).sub_const origin).const_mul barrierA).exp).const_mul
          epsilon)
    convert hraw using 1
    simp only [a]
    ring
  have hpsi : HasDerivAt psi (barrierB * psi t) t := by
    have hraw : HasDerivAt psi
        ((kappa * epsilon) *
          (Real.exp (barrierB * (t - origin)) * barrierB)) t := by
      simpa only [psi, id_eq, mul_one] using
        (((((hasDerivAt_id t).sub_const origin).const_mul barrierB).exp).const_mul
          (kappa * epsilon))
    convert hraw using 1
    simp only [psi]
    ring
  let W₀ : StrongDual Real (TangentSpace I x) :=
    tensor0SOneFormToStrongDual (I := I) z.2
  obtain ⟨testU, testUTensor, testW, htestUTensor, htestUJoint,
      htestWJoint, htestUValue, htestWValue, hexact⟩ :=
    hamilton_perturbed_harnack_block_exact_evolution
      (I := I) S hS clock (hreg ht) x basis horth z.1 W₀ a psi htilde
        (barrierA * a t) (barrierB * psi t) ha hpsi htildeSmooth
  let extension : Real → ∀ y,
      HarnackCarrierFiber (E := E) (I := I) (M := M) y :=
    fun r y ↦ (testU r y, testW r y)
  let f : Real → M → Real := fun r y ↦
    inner0S (I := I) (S.base.metric r) y 4
        (Tensor0SField.domDomCongr ∞ curvatureSlotSwap
          (S.base.rm04 r) y)
        ((testUTensor r y).product (testUTensor r y)) +
      2 * inner0S (I := I) (S.base.metric r) y 3
        (hamiltonPField (I := I) (S.base.metric r) y)
        ((testUTensor r y).product (testW r y)) +
      inner0S (I := I) (S.base.metric r) y 2
        (hamiltonMOriginField (I := I) origin r (S.base.metric r) y)
        ((testW r y).product (testW r y)) +
      a r / (r - origin) *
        (htilde y * normSq0S (I := I) (S.base.metric r) y 1 (testW r y)) +
      psi r * normSq0S (I := I) (S.base.metric r) y 2 (testUTensor r y)
  let timeDeriv : Real := deriv (fun r : Real ↦ f r x) t
  have htestWBase : testW t x = z.2 := by
    ext slots
    calc
      testW t x slots = testW t x (fun _ : Fin 1 ↦ slots 0) := by
        congr 1
        funext i
        fin_cases i
        rfl
      _ = W₀ (slots 0) := htestWValue (slots 0)
      _ = z.2 (fun _ : Fin 1 ↦ slots 0) :=
        tensor0SOneFormToStrongDual_apply (I := I) z.2 (slots 0)
      _ = z.2 slots := by
        congr 1
        funext i
        fin_cases i
        rfl
  have htestUTensorBase : testUTensor t x = z.1.toTensor0S := by
    rw [← htestUTensor t x, htestUValue]
  have hextension : extension t x = z := by
    apply Prod.ext
    · exact htestUValue
    · exact htestWBase
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, hamiltonPerturbedHarnackQuadraticValue_zero] at hnull
    norm_num at hnull
  have hbaseNe : (testU t x, testW t x) ≠ 0 := by
    intro hzero
    apply hz
    rw [← hextension]
    exact hzero
  have hfSmooth : ContMDiff I 𝓘(Real, Real) ∞ (f t) := by
    exact hamilton_perturbed_test_scalar_contMDiff
      (I := I) S origin t (testUTensor t) (testW t) (a t) (psi t)
        htilde htildeSmooth
  have hextensionNear : ∀ᶠ p in nhds (t, x), extension p.1 p.2 ≠ 0 := by
    exact hamilton_test_carrier_eventually_ne_zero
      (I := I) t x testU testUTensor testW
        htestUTensor htestUJoint htestWJoint hbaseNe
  have hupperWithin : ∀ᶠ p in nhdsWithin (t, x)
      (Set.Ioc origin stop ×ˢ Set.univ),
      hamiltonPerturbedHarnackQuadraticValue
        (E := E) (I := I) (M := M) S origin
        (hamiltonBarrierPhi epsilon barrierA origin h)
        (hamiltonBarrierPsi kappa epsilon barrierB origin)
          p.1 p.2 (extension p.1 p.2) ≤ f p.1 p.2 := by
    have hspace : Filter.Tendsto (fun p : Real × M ↦ p.2)
        (nhdsWithin (t, x) (Set.Ioc origin stop ×ˢ Set.univ))
        (nhds x) := continuousAt_snd.mono_left inf_le_left
    filter_upwards [hextensionNear.filter_mono inf_le_left, hspace hUpper,
      self_mem_nhdsWithin] with p hpne hpUpper hpDomain
    have hpReg : p.1 ∈ D.regular := by
      exact hreg hpDomain.1
    have hpOrigin : origin < p.1 := hpDomain.1.1
    rw [hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
      S origin (hamiltonBarrierPhi epsilon barrierA origin h)
        (hamiltonBarrierPsi kappa epsilon barrierB origin)
          p.1 hpOrigin p.2 (extension p.1 p.2) hpne]
    change hamiltonPerturbedHarnackQuadraticAt (I := I) S
        ⟨origin, p.1, hpOrigin⟩
          (hamiltonBarrierPhi epsilon barrierA origin h p.1 p.2)
          (hamiltonBarrierPsi kappa epsilon barrierB origin p.1)
          p.2 (testU p.1 p.2) (testW p.1 p.2) ≤ f p.1 p.2
    have hfQp : f p.1 p.2 =
        hamiltonPerturbedHarnackQuadraticAt (I := I) S
          ⟨origin, p.1, hpOrigin⟩
            (a p.1 * htilde p.2) (psi p.1) p.2
            (testU p.1 p.2) (testW p.1 p.2) := by
      rw [hamiltonPerturbedHarnackQuadraticAt_eq_inner
        (I := I) S hS ⟨origin, p.1, hpOrigin⟩ hpReg]
      simp only [f, htestUTensor, hamiltonMField, HarnackClock.elapsed,
        normSq0S_eq_inner, Tensor0SField.domDomCongr_apply]
      ring_nf
    rw [hfQp]
    have hfactorNonneg :
        0 ≤ epsilon * Real.exp (barrierA * (p.1 - origin)) := by
      positivity
    have hphiLe :
        epsilon * Real.exp (barrierA * (p.1 - origin)) * h p.2 ≤
          epsilon * Real.exp (barrierA * (p.1 - origin)) * htilde p.2 :=
      mul_le_mul_of_nonneg_left hpUpper hfactorNonneg
    have hshiftLe :
        (epsilon * Real.exp (barrierA * (p.1 - origin)) * h p.2 /
            (p.1 - origin)) *
              normSq0S (I := I) (S.base.metric p.1) p.2 1 (testW p.1 p.2) ≤
          (epsilon * Real.exp (barrierA * (p.1 - origin)) * htilde p.2 /
            (p.1 - origin)) *
              normSq0S (I := I) (S.base.metric p.1) p.2 1
                (testW p.1 p.2) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hphiLe (sub_nonneg.mpr hpOrigin.le))
        (normSq0S_nonneg (I := I) (S.base.metric p.1) p.2 1
          (testW p.1 p.2))
    unfold hamiltonPerturbedHarnackQuadraticAt
    dsimp only [hamiltonBarrierPhi, hamiltonBarrierPsi, a, psi,
      HarnackClock.elapsed]
    linarith only [hshiftLe]
  have htime : HasDerivWithinAt (fun r : Real ↦ f r x) timeDeriv
      (Set.Ioc origin stop) t := by
    have htimeAt : HasDerivAt (fun r : Real ↦ f r x) timeDeriv t := by
      simpa only [f, timeDeriv] using hexact.1
    exact htimeAt.hasDerivWithinAt
  have hlapEq : laplacian (I := I)
      (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t) htilde x =
        laplacian (I := I) (LeviCivita (I := I) (S.base.metric t))
          (S.base.metric t) hbar x :=
    laplacian_congr_of_eventuallyEq (I := I)
      (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t)
      htildeSmooth.contMDiffAt
      ((hbarSmooth x hxU).contMDiffAt (hU.mem_nhds hxU)) htildeEq
  let phi0 : Real := a t * htilde x
  let Lphi0 : Real := barrierA * a t * htilde x - a t *
    laplacian (I := I) (LeviCivita (I := I) (S.base.metric t))
      (S.base.metric t) htilde x
  let psi0 : Real := psi t
  have hphi0 : 0 ≤ phi0 := by
    have hhtilde : 0 ≤ htilde x := by
      rw [htildeEqX, hbarEq]
      exact (zero_le_one.trans (hh x))
    exact mul_nonneg (by dsimp only [a]; positivity) hhtilde
  have hpsi0 : 0 ≤ psi0 := by
    dsimp only [psi0, psi]
    positivity
  have hpsi0one : psi0 ≤ 1 := by
    simpa only [psi0, psi, hamiltonBarrierPsi] using hpsi1
  have hphiPsi : reactionC * psi0 < phi0 := by
    have hraw := hamilton_barrier_phi_gt_control_mul_psi
      (M := M) (x := x) ht.1.le ht.2 hepsilon (hh x) hsmall
    simpa only [phi0, psi0, a, psi, htildeEqX, hbarEq,
      hamiltonBarrierPhi, hamiltonBarrierPsi] using hraw
  have hLphi : reactionC * phi0 < Lphi0 := by
    have hlap : laplacian (I := I)
        (LeviCivita (I := I) (S.base.metric t))
          (S.base.metric t) htilde x ≤ Ch * htilde x := by
      rw [hlapEq, htildeEqX, hbarEq]
      exact hbarLap
    have hraw := hamilton_barrier_supported_phi_heat_gt_control_mul_phi
      (origin := origin) (t := t) hCA hepsilon
        (by simpa only [htildeEqX, hbarEq] using hh x) hlap
    dsimp only [phi0, Lphi0, a]
    nlinarith only [hraw]
  have hpsiDeriv : reactionC * psi0 < barrierB * psi0 := by
    simpa only [psi0, psi, hamiltonBarrierPsi] using
      (hamilton_barrier_psi_derivative_gt_control_mul_psi
        hCB hkappa hepsilon :
          reactionC * hamiltonBarrierPsi kappa epsilon barrierB origin t <
            barrierB * hamiltonBarrierPsi kappa epsilon barrierB origin t)
  have hWcoefficient : 0 < Lphi0 / clock.elapsed +
      phi0 / clock.elapsed ^ 2 - reactionC * psi0 / clock.elapsed ^ 2 -
        reactionC * phi0 / clock.elapsed := by
    have hfirst : 0 < (Lphi0 - reactionC * phi0) / clock.elapsed :=
      div_pos (sub_pos.mpr hLphi) clock.elapsed_pos
    have hsecond : 0 < (phi0 - reactionC * psi0) / clock.elapsed ^ 2 :=
      div_pos (sub_pos.mpr hphiPsi) (sq_pos_of_pos clock.elapsed_pos)
    rw [show Lphi0 / clock.elapsed + phi0 / clock.elapsed ^ 2 -
        reactionC * psi0 / clock.elapsed ^ 2 -
          reactionC * phi0 / clock.elapsed =
        (Lphi0 - reactionC * phi0) / clock.elapsed +
          (phi0 - reactionC * psi0) / clock.elapsed ^ 2 by ring]
    exact add_pos hfirst hsecond
  have hQnonnegative : ∀
      (U₀ : HamiltonHarnackTwoForm (TangentSpace I x))
      (W : Tensor0SSpace 1 I x),
      0 ≤ hamiltonPerturbedHarnackQuadraticAt
        (I := I) S clock phi0 psi0 x U₀ W := by
    intro U₀ W
    by_cases hcarrier : (U₀, W) = 0
    · have hU₀ : U₀ = 0 := congrArg Prod.fst hcarrier
      have hW : W = 0 := congrArg Prod.snd hcarrier
      rw [hU₀, hW]
      have hscale := hamiltonPerturbedHarnackQuadraticAt_smul
        (I := I) S clock phi0 psi0 x 0 U₀ W
      have hzero : hamiltonPerturbedHarnackQuadraticAt
          (I := I) S clock phi0 psi0 x 0 0 = 0 := by
        simpa using hscale
      exact hzero.ge
    · have hvalue := hnonnegative x (U₀, W)
      rw [hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
        S origin (hamiltonBarrierPhi epsilon barrierA origin h)
          (hamiltonBarrierPsi kappa epsilon barrierB origin)
            t ht.1 x (U₀, W) hcarrier] at hvalue
      simpa only [phi0, psi0, a, psi, htildeEqX, hbarEq,
        hamiltonBarrierPhi, hamiltonBarrierPsi] using hvalue
  have hQzero : hamiltonPerturbedHarnackQuadraticAt
      (I := I) S clock phi0 psi0 x z.1 z.2 = 0 := by
    have hvalueZero := hnull
    rw [hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
      S origin (hamiltonBarrierPhi epsilon barrierA origin h)
        (hamiltonBarrierPsi kappa epsilon barrierB origin) t ht.1 x z hz] at hvalueZero
    simpa only [phi0, psi0, a, psi, htildeEqX, hbarEq,
      hamiltonBarrierPhi, hamiltonBarrierPsi] using hvalueZero
  have hRhs := hamilton_perturbed_harnack_exact_rhs_pos_of_null
    (I := I) S hS clock (hreg ht) x basis horth reactionK S0 reactionB reactionC
      phi0 Lphi0 psi0 (barrierB * psi0) hS0 (by
        simpa only [clock, HarnackClock.elapsed] using helapsed)
      (fun k hk ↦ hderiv k hk x) (by
        simpa only using hReactionB) (by simpa only using hReactionCphi)
      (by simpa only using hReactionCpsiW) (by simpa only using hReactionCpsiU)
      hphi0 hpsi0 hpsi0one hQnonnegative z.1 z.2 hQzero hz
      hWcoefficient (sub_pos.mpr hpsiDeriv)
  have hstrict : 0 < timeDeriv - laplacian (I := I)
      (LeviCivita (I := I) (S.base.metric t))
        (S.base.metric t) (f t) x := by
    have hevolution := hexact.2
    have hWcomp (i : Fin (Module.finrank Real E)) :
        z.2 (fun _ : Fin 1 ↦ basis i) = z.2 ![basis i] := by
      congr 1
      funext j
      fin_cases j
      rfl
    have hevolution' : timeDeriv - laplacian (I := I)
        (LeviCivita (I := I) (S.base.metric t))
          (S.base.metric t) (f t) x =
        hamiltonBlockJ
            (fun i j k l ↦ S.base.rm04 t x
              (vec4 (I := I) (basis i) (basis j) (basis l) (basis k)))
            (fun i j k ↦ hamiltonPField (I := I)
              (S.base.metric t) x
                (vec3 (I := I) (basis i) (basis j) (basis k)))
            (fun i j ↦ hamiltonMOriginField (I := I) origin t
              (S.base.metric t) x (vec2 (I := I) (basis i) (basis j)))
            (fun i j ↦ z.1 ![basis i, basis j])
            (fun i ↦ z.2 ![basis i]) +
          hamiltonBlockSigmaSquare
            (fun i j k l ↦ S.base.rm04 t x
              (vec4 (I := I) (basis i) (basis j) (basis l) (basis k)))
            (fun i j k ↦ hamiltonPField (I := I)
              (S.base.metric t) x
                (vec3 (I := I) (basis i) (basis j) (basis k)))
            (fun i j ↦ z.1 ![basis i, basis j])
            (fun i ↦ z.2 ![basis i]) +
          (Lphi0 / clock.elapsed + phi0 / clock.elapsed ^ 2) *
            (∑ i, (z.2 ![basis i]) ^ 2) +
          barrierB * psi0 *
            (∑ i, ∑ j, (z.1 ![basis i, basis j]) ^ 2) -
          2 * psi0 *
            (∑ e, ∑ i, ∑ j,
              (hamiltonTestJetDU clock
                (fun p q ↦ metricRicci (I := I) (M := M)
                  (S.base.metric t) x
                    (vec2 (I := I) (basis p) (basis q)))
                (fun p q ↦ if p = q then (1 : Real) else 0)
                (fun p ↦ z.2 ![basis p]) e i j) ^ 2) := by
      simpa only [f, timeDeriv, clock, phi0, Lphi0, psi0,
        W₀, tensor0SOneFormToStrongDual_apply, hWcomp, hamiltonBarrierPhi,
        hamiltonBarrierPsi, laplacianAt, flowG, SolutionFamily.connection,
        LeviCivita] using hevolution
    rw [hevolution']
    exact hRhs
  have hvalue : f t x = hamiltonPerturbedHarnackQuadraticValue
      (E := E) (I := I) (M := M) S origin
      (hamiltonBarrierPhi epsilon barrierA origin h)
      (hamiltonBarrierPsi kappa epsilon barrierB origin)
        t x (extension t x) := by
    rw [hextension]
    rw [hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
      S origin (hamiltonBarrierPhi epsilon barrierA origin h)
        (hamiltonBarrierPsi kappa epsilon barrierB origin) t ht.1 x z hz]
    have hfQt : f t x = hamiltonPerturbedHarnackQuadraticAt
        (I := I) S clock phi0 psi0 x z.1 z.2 := by
      rw [hamiltonPerturbedHarnackQuadraticAt_eq_inner
        (I := I) S hS clock (hreg ht)]
      simp only [f, clock, phi0, psi0, a, psi, htestUTensorBase,
        htestWBase, htildeEqX, hbarEq, hamiltonMField,
        HarnackClock.elapsed, normSq0S_eq_inner,
        Tensor0SField.domDomCongr_apply]
      ring_nf
    simpa only [clock, phi0, psi0, a, psi, htildeEqX, hbarEq,
      hamiltonBarrierPhi, hamiltonBarrierPsi] using hfQt
  refine ⟨extension, f, timeDeriv, hextension, hvalue, hupperWithin, htime,
    hfSmooth.mdifferentiableAt (by simp),
    Filter.Eventually.of_forall (fun y ↦ hfSmooth.mdifferentiableAt (by simp)),
    gradientFun_mdiffAt (I := I) (S.base.metric t) hfSmooth x, hstrict⟩

private theorem exists_hamilton_barrier_early_interval
    {B n kappa epsilon S : Real}
    (hB : 0 <= B) (hn : 0 <= n) (hkappa : 0 < kappa)
    (hepsilon : 0 < epsilon) (hS : 0 < S) :
    exists eta : Real, 0 < eta ∧ eta <= S ∧
      forall tau phi psi : Real, 0 < tau -> tau <= eta ->
        epsilon <= phi -> kappa * epsilon <= psi ->
        0 < phi / tau - B * n - 2 * B ^ 2 * n ^ 3 / psi := by
  let D := B * n + 2 * B ^ 2 * n ^ 3 / (kappa * epsilon)
  have hke : 0 < kappa * epsilon := mul_pos hkappa hepsilon
  have hD : 0 <= D := by
    dsimp only [D]
    positivity
  let eta := min S (epsilon / (2 * (D + 1)))
  have hden : 0 < 2 * (D + 1) := by positivity
  have heta : 0 < eta := lt_min hS (div_pos hepsilon hden)
  refine ⟨eta, heta, min_le_left _ _, ?_⟩
  intro tau phi psi htau htauEta hphi hpsi
  have htauRatio : tau <= epsilon / (2 * (D + 1)) :=
    htauEta.trans (min_le_right _ _)
  have hDmul : D * tau < epsilon := by
    calc
      D * tau <= D * (epsilon / (2 * (D + 1))) :=
        mul_le_mul_of_nonneg_left htauRatio hD
      _ < epsilon := by
        rw [show D * (epsilon / (2 * (D + 1))) =
          D * epsilon / (2 * (D + 1)) by ring]
        apply (div_lt_iff₀ hden).2
        nlinarith [mul_pos hepsilon (show 0 < D + 2 by linarith)]
  have hDdiv : D < epsilon / tau := (lt_div_iff₀ htau).2 hDmul
  have hphiDiv : epsilon / tau <= phi / tau :=
    div_le_div_of_nonneg_right hphi htau.le
  have hnum : 0 <= 2 * B ^ 2 * n ^ 3 := by positivity
  have hfrac :
      2 * B ^ 2 * n ^ 3 / psi <=
        2 * B ^ 2 * n ^ 3 / (kappa * epsilon) :=
    div_le_div_of_nonneg_left hnum hke hpsi
  dsimp only [D] at hDdiv
  linarith

private theorem hamilton_barrier_tail_coefficient_pos
    {B n kappa epsilon S tau h phi psi : Real}
    (hB : 0 <= B) (hn : 0 <= n) (hkappa : 0 < kappa)
    (hepsilon : 0 < epsilon) (hS : 0 < S)
    (htau : 0 < tau) (htauS : tau <= S)
    (hphi : epsilon * h <= phi) (hpsi : kappa * epsilon <= psi)
    (hh : S / epsilon *
        (B * n + 2 * B ^ 2 * n ^ 3 / (kappa * epsilon) + 1) < h) :
    0 < phi / tau - B * n - 2 * B ^ 2 * n ^ 3 / psi := by
  have hke : 0 < kappa * epsilon := mul_pos hkappa hepsilon
  have hD : 0 <= B * n + 2 * B ^ 2 * n ^ 3 / (kappa * epsilon) := by
    positivity
  have hhpos : 0 < h := by
    have : 0 <= S / epsilon *
        (B * n + 2 * B ^ 2 * n ^ 3 / (kappa * epsilon) + 1) := by
      positivity
    linarith
  have hscale :
      B * n + 2 * B ^ 2 * n ^ 3 / (kappa * epsilon) + 1 <
        epsilon * h / S := by
    apply (lt_div_iff₀ hS).2
    calc
      (B * n + 2 * B ^ 2 * n ^ 3 / (kappa * epsilon) + 1) * S =
          epsilon * (S / epsilon *
            (B * n + 2 * B ^ 2 * n ^ 3 / (kappa * epsilon) + 1)) := by
        field_simp
      _ < epsilon * h := mul_lt_mul_of_pos_left hh hepsilon
  have hphiTau : epsilon * h / S <= phi / tau := by
    have hfirst : epsilon * h / S <= epsilon * h / tau := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg hepsilon.le hhpos.le) htau htauS
    exact hfirst.trans (div_le_div_of_nonneg_right hphi htau.le)
  have hnum : 0 <= 2 * B ^ 2 * n ^ 3 := by positivity
  have hfrac :
      2 * B ^ 2 * n ^ 3 / psi <=
        2 * B ^ 2 * n ^ 3 / (kappa * epsilon) :=
    div_le_div_of_nonneg_left hnum hke hpsi
  linarith

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackQuadraticAt_pos_of_lower_bound
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (clock : HarnackClock) (x : M)
    (phi psi coefficient : Real)
    (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x)
    (hpsi : 0 < psi) (hcoefficient : 0 < coefficient)
    (hne : (U, W) ≠ 0)
    (hlower :
      hamiltonPerturbedHarnackQuadraticAt (I := I) S clock phi psi x U W >=
        psi / 2 * normSq0S (I := I) (S.base.metric clock.time) x 2
            U.toTensor0S +
          coefficient *
            normSq0S (I := I) (S.base.metric clock.time) x 1 W) :
    0 < hamiltonPerturbedHarnackQuadraticAt
      (I := I) S clock phi psi x U W := by
  by_cases hU : U = 0
  · have hW : W ≠ 0 := by
      intro hW
      apply hne
      simp [hU, hW]
    have hfirst : 0 <=
        psi / 2 * normSq0S (I := I) (S.base.metric clock.time) x 2
          U.toTensor0S :=
      mul_nonneg (div_nonneg hpsi.le (by norm_num))
        (normSq0S_nonneg (I := I) (S.base.metric clock.time) x 2 U.toTensor0S)
    have hsecond : 0 < coefficient *
        normSq0S (I := I) (S.base.metric clock.time) x 1 W :=
      mul_pos hcoefficient
        ((tensor0SMetricData (I := I) (S.base.metric clock.time) x 1).inner_pos_of_ne_zero
          hW)
    exact (add_pos_of_nonneg_of_pos hfirst hsecond).trans_le hlower
  · have hfirst : 0 <
        psi / 2 * normSq0S (I := I) (S.base.metric clock.time) x 2
          U.toTensor0S :=
      mul_pos (div_pos hpsi (by norm_num))
        ((tensor0SMetricData (I := I) (S.base.metric clock.time) x 2).inner_pos_of_ne_zero
          (harnackTwoForm_toTensor0S_ne_zero (I := I) hU))
    have hsecond : 0 <= coefficient *
        normSq0S (I := I) (S.base.metric clock.time) x 1 W :=
      mul_nonneg hcoefficient.le
        (normSq0S_nonneg (I := I) (S.base.metric clock.time) x 1 W)
    exact (add_pos_of_pos_of_nonneg hfirst hsecond).trans_le hlower

private theorem exists_hamiltonPerturbedHarnackQuadratic_barrier_localization
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alphaMinus origin stop C A B kappa epsilon : Real}
    (hbuffer : alphaMinus < origin)
    (horiginStop : origin < stop)
    (hslab : Set.Icc alphaMinus stop ⊆ D.carrier)
    (hreg : Set.Ioc alphaMinus stop ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric alphaMinus))
    (hC : 0 <= C)
    (hcurv : forall t, t ∈ Set.Icc alphaMinus stop -> forall x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) <= C)
    (hR : forall t, t ∈ Set.Icc origin stop -> forall x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hA : 0 <= A) (hB : 0 <= B) (hkappa : 0 < kappa)
    (hepsilon : 0 < epsilon)
    (h : M -> Real) (hproper : IsProperMap h) (hh : forall x, 1 <= h x) :
    exists eta : Real, exists K : Set M,
      0 < eta ∧ eta <= stop - origin ∧ IsCompact K ∧
        (forall clock : HarnackClock, clock.origin = origin ->
          clock.time ∈ Set.Ioc origin (origin + eta) -> forall x : M,
          forall U : HamiltonHarnackTwoForm (TangentSpace I x),
          forall W : Tensor0SSpace 1 I x, (U, W) ≠ 0 ->
            0 < hamiltonPerturbedHarnackQuadraticAt (I := I) S
              clock
              (hamiltonBarrierPhi epsilon A origin h clock.time x)
              (hamiltonBarrierPsi kappa epsilon B origin clock.time) x U W) ∧
        (forall clock : HarnackClock, clock.origin = origin ->
          clock.time ∈ Set.Icc (origin + eta) stop -> forall x : M,
          x ∉ K -> forall U : HamiltonHarnackTwoForm (TangentSpace I x),
          forall W : Tensor0SSpace 1 I x, (U, W) ≠ 0 ->
            0 < hamiltonPerturbedHarnackQuadraticAt (I := I) S
              clock
              (hamiltonBarrierPhi epsilon A origin h clock.time x)
              (hamiltonBarrierPsi kappa epsilon B origin clock.time) x U W) := by
  obtain ⟨B0, hB0, hlower⟩ :=
    exists_hamiltonPerturbedHarnackQuadratic_slab_lower_bound
      (I := I) S hS hbuffer horiginStop.le hslab hreg hcomplete hC hcurv hR
  let n : Real := Module.finrank Real E
  have hn : 0 <= n := by positivity
  obtain ⟨eta, heta, hetaS, hearlyCoefficient⟩ :=
    exists_hamilton_barrier_early_interval hB0 hn hkappa hepsilon
      (sub_pos.mpr horiginStop)
  let threshold : Real := (stop - origin) / epsilon *
    (B0 * n + 2 * B0 ^ 2 * n ^ 3 / (kappa * epsilon) + 1)
  let K : Set M := h ⁻¹' Set.Icc 1 threshold
  have hK : IsCompact K := hproper.isCompact_preimage isCompact_Icc
  refine ⟨eta, K, heta, hetaS, hK, ?_, ?_⟩
  · intro clock hclock ht x U W hne
    rcases ht with ⟨htorigin, htupper⟩
    have htstop : clock.time <= stop := by linarith
    have htime : clock.time ∈ Set.Icc origin stop := ⟨htorigin.le, htstop⟩
    have htau : 0 < clock.elapsed := clock.elapsed_pos
    have htauEta : clock.elapsed <= eta := by
      rw [HarnackClock.elapsed, hclock]
      linarith
    have hAexp : 1 <= Real.exp (A * (clock.time - origin)) :=
      Real.one_le_exp (mul_nonneg hA (sub_nonneg.mpr htorigin.le))
    have hBexp : 1 <= Real.exp (B * (clock.time - origin)) :=
      Real.one_le_exp (mul_nonneg hB (sub_nonneg.mpr htorigin.le))
    have hphi : epsilon <=
        hamiltonBarrierPhi epsilon A origin h clock.time x := by
      calc
        epsilon <= epsilon * Real.exp (A * (clock.time - origin)) := by
          simpa using mul_le_mul_of_nonneg_left hAexp hepsilon.le
        _ = epsilon * Real.exp (A * (clock.time - origin)) * 1 := by ring
        _ <= epsilon * Real.exp (A * (clock.time - origin)) * h x :=
          mul_le_mul_of_nonneg_left (hh x)
            (mul_nonneg hepsilon.le (Real.exp_nonneg _))
        _ = hamiltonBarrierPhi epsilon A origin h clock.time x := rfl
    have hpsiLower : kappa * epsilon <=
        hamiltonBarrierPsi kappa epsilon B origin clock.time := by
      calc
        kappa * epsilon = kappa * epsilon * 1 := by ring
        _ <= kappa * epsilon * Real.exp (B * (clock.time - origin)) :=
          mul_le_mul_of_nonneg_left hBexp (mul_pos hkappa hepsilon).le
        _ = hamiltonBarrierPsi kappa epsilon B origin clock.time := rfl
    have hpsi : 0 <
        hamiltonBarrierPsi kappa epsilon B origin clock.time := by
      unfold hamiltonBarrierPsi
      positivity
    have hcoefficient := hearlyCoefficient clock.elapsed
      (hamiltonBarrierPhi epsilon A origin h clock.time x)
      (hamiltonBarrierPsi kappa epsilon B origin clock.time)
      htau htauEta hphi hpsiLower
    have hQ := hlower clock htime x
      (hamiltonBarrierPhi epsilon A origin h clock.time x)
      (hamiltonBarrierPsi kappa epsilon B origin clock.time) hpsi U W
    exact hamiltonPerturbedHarnackQuadraticAt_pos_of_lower_bound
      (I := I) S clock x _ _ _ U W hpsi hcoefficient hne hQ
  · intro clock hclock ht x hxK U W hne
    rcases ht with ⟨htlower, htstop⟩
    have horiginT : origin < clock.time :=
      lt_of_lt_of_le (lt_add_of_pos_right origin heta) htlower
    have htime : clock.time ∈ Set.Icc origin stop :=
      ⟨horiginT.le, htstop⟩
    have htau : 0 < clock.elapsed := clock.elapsed_pos
    have htauS : clock.elapsed <= stop - origin := by
      rw [HarnackClock.elapsed, hclock]
      linarith
    have hxThreshold : threshold < h x := by
      by_contra hnot
      apply hxK
      exact ⟨hh x, le_of_not_gt hnot⟩
    have hAexp : 1 <= Real.exp (A * (clock.time - origin)) :=
      Real.one_le_exp (mul_nonneg hA (sub_nonneg.mpr horiginT.le))
    have hBexp : 1 <= Real.exp (B * (clock.time - origin)) :=
      Real.one_le_exp (mul_nonneg hB (sub_nonneg.mpr horiginT.le))
    have hphi : epsilon * h x <=
        hamiltonBarrierPhi epsilon A origin h clock.time x := by
      calc
        epsilon * h x = epsilon * 1 * h x := by ring
        _ <= epsilon * Real.exp (A * (clock.time - origin)) * h x := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hAexp hepsilon.le) (le_trans zero_le_one (hh x))
        _ = hamiltonBarrierPhi epsilon A origin h clock.time x := rfl
    have hpsiLower : kappa * epsilon <=
        hamiltonBarrierPsi kappa epsilon B origin clock.time := by
      calc
        kappa * epsilon = kappa * epsilon * 1 := by ring
        _ <= kappa * epsilon * Real.exp (B * (clock.time - origin)) :=
          mul_le_mul_of_nonneg_left hBexp (mul_pos hkappa hepsilon).le
        _ = hamiltonBarrierPsi kappa epsilon B origin clock.time := rfl
    have hpsi : 0 <
        hamiltonBarrierPsi kappa epsilon B origin clock.time := by
      unfold hamiltonBarrierPsi
      positivity
    have hcoefficient := hamilton_barrier_tail_coefficient_pos
      hB0 hn hkappa hepsilon (sub_pos.mpr horiginStop)
      htau htauS hphi hpsiLower (by
        simpa only [threshold, n] using hxThreshold)
    have hQ := hlower clock htime x
      (hamiltonBarrierPhi epsilon A origin h clock.time x)
      (hamiltonBarrierPsi kappa epsilon B origin clock.time) hpsi U W
    exact hamiltonPerturbedHarnackQuadraticAt_pos_of_lower_bound
      (I := I) S clock x _ _ _ U W hpsi hcoefficient hne hQ

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackRayleigh_compact_representatives
    [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (origin stop eta : Real) (phi : Real -> M -> Real) (psi : Real -> Real)
    (gRef : SmoothRiemannianMetric I M) (K : Set M)
    (heta : 0 < eta) (hK : IsCompact K)
    (hearly : forall clock : HarnackClock, clock.origin = origin ->
      clock.time ∈ Set.Ioc origin (origin + eta) -> forall x : M,
      forall U : HamiltonHarnackTwoForm (TangentSpace I x),
      forall W : Tensor0SSpace 1 I x, (U, W) ≠ 0 ->
        0 < hamiltonPerturbedHarnackQuadraticAt (I := I) S clock
          (phi clock.time x) (psi clock.time) x U W)
    (htail : forall clock : HarnackClock, clock.origin = origin ->
      clock.time ∈ Set.Icc (origin + eta) stop -> forall x : M,
      x ∉ K -> forall U : HamiltonHarnackTwoForm (TangentSpace I x),
      forall W : Tensor0SSpace 1 I x, (U, W) ≠ 0 ->
        0 < hamiltonPerturbedHarnackQuadraticAt (I := I) S clock
          (phi clock.time x) (psi clock.time) x U W) :
    let L : Set (HarnackCarrierTotal (E := E) (I := I) (M := M)) :=
      {z | z.proj ∈ K ∧
        harnackCarrierNormSq (E := E) (I := I) (M := M) gRef z = 1}
    IsCompact L ∧
      (forall t, t ∈ Set.Ioc origin (origin + eta) -> forall x : M,
        forall z : HarnackCarrierFiber (E := E) (I := I) (M := M) x,
          0 < hamiltonPerturbedHarnackRayleigh
            (E := E) (I := I) (M := M) S origin phi psi gRef t x z) ∧
      (forall t, t ∈ Set.Icc (origin + eta) stop ->
        forall z : HarnackCarrierTotal (E := E) (I := I) (M := M),
          hamiltonPerturbedHarnackRayleigh
              (E := E) (I := I) (M := M) S origin phi psi gRef
                t z.proj z.2 <= 0 ->
            exists w, w ∈ L ∧
              hamiltonPerturbedHarnackRayleigh
                  (E := E) (I := I) (M := M) S origin phi psi gRef
                    t w.proj w.2 <= 0 ∧
                (hamiltonPerturbedHarnackRayleigh
                    (E := E) (I := I) (M := M) S origin phi psi gRef
                      t z.proj z.2 < 0 ->
                  hamiltonPerturbedHarnackRayleigh
                    (E := E) (I := I) (M := M) S origin phi psi gRef
                      t w.proj w.2 < 0)) := by
  dsimp only
  let L : Set (HarnackCarrierTotal (E := E) (I := I) (M := M)) :=
    {z | z.proj ∈ K ∧
      harnackCarrierNormSq (E := E) (I := I) (M := M) gRef z = 1}
  have hL : IsCompact L := harnackCarrierNormSq_level_isCompact
    (E := E) (I := I) (M := M) gRef hK
  refine ⟨hL, ?_, ?_⟩
  · intro t ht x z
    by_cases hz : z = 0
    · subst z
      rw [hamiltonPerturbedHarnackRayleigh_zero]
      norm_num
    · let clock : HarnackClock := ⟨origin, t, ht.1⟩
      have hQ : 0 < hamiltonPerturbedHarnackQuadraticAt (I := I) S clock
          (phi t x) (psi t) x z.1 z.2 :=
        hearly clock rfl ht x z.1 z.2 hz
      have hnorm : 0 <
          harnackCarrierNormSq (E := E) (I := I) (M := M) gRef
            (Bundle.TotalSpace.mk'
              (HarnackCarrierModel (E := E)) x z) :=
        harnackCarrierNormSq_pos (E := E) (I := I) (M := M) gRef
          (Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) x z) hz
      classical
      simp only [hamiltonPerturbedHarnackRayleigh, dif_pos ht.1, if_neg hz]
      exact div_pos hQ hnorm
  · intro t ht z hzq
    have horiginT : origin < t :=
      lt_of_lt_of_le (lt_add_of_pos_right origin heta) ht.1
    have hz : z.2 ≠ 0 := by
      intro hz0
      have hqone := hamiltonPerturbedHarnackRayleigh_zero
        (E := E) (I := I) (M := M) S origin phi psi gRef t z.proj
      rw [hz0, hqone] at hzq
      norm_num at hzq
    let clock : HarnackClock := ⟨origin, t, horiginT⟩
    have hzbase : z.proj ∈ K := by
      by_contra hzK
      have hQ : 0 < hamiltonPerturbedHarnackQuadraticAt (I := I) S clock
          (phi t z.proj) (psi t) z.proj z.2.1 z.2.2 :=
        htail clock rfl ht z.proj hzK z.2.1 z.2.2 hz
      have hnorm : 0 <
          harnackCarrierNormSq (E := E) (I := I) (M := M) gRef z :=
        harnackCarrierNormSq_pos (E := E) (I := I) (M := M) gRef z hz
      have hqpos : 0 < hamiltonPerturbedHarnackRayleigh
          (E := E) (I := I) (M := M) S origin phi psi gRef
            t z.proj z.2 := by
        classical
        simp only [hamiltonPerturbedHarnackRayleigh,
          dif_pos horiginT, if_neg hz]
        exact div_pos hQ hnorm
      exact (not_lt_of_ge hzq) hqpos
    let zn := normalizeHarnackCarrier
      (E := E) (I := I) (M := M) gRef z.proj z.2
    let w : HarnackCarrierTotal (E := E) (I := I) (M := M) :=
      Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) z.proj zn
    have hwnorm : harnackCarrierNormSq
        (E := E) (I := I) (M := M) gRef w = 1 := by
      exact normalizeHarnackCarrier_normSq
        (E := E) (I := I) (M := M) gRef z.proj z.2 hz
    have hwL : w ∈ L := ⟨hzbase, hwnorm⟩
    have hqeq : hamiltonPerturbedHarnackRayleigh
          (E := E) (I := I) (M := M) S origin phi psi gRef
            t w.proj w.2 =
        hamiltonPerturbedHarnackRayleigh
          (E := E) (I := I) (M := M) S origin phi psi gRef
            t z.proj z.2 := by
      exact hamiltonPerturbedHarnackRayleigh_normalize
        (E := E) (I := I) (M := M) S origin phi psi gRef
          t horiginT z.proj z.2 hz
    refine ⟨w, hwL, ?_, ?_⟩
    · rwa [hqeq]
    · intro hstrict
      rwa [hqeq]

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackQuadraticValue_compact_representatives
    [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (origin stop eta : Real) (phi : Real -> M -> Real) (psi : Real -> Real)
    (gRef : SmoothRiemannianMetric I M) (K : Set M)
    (heta : 0 < eta) (hK : IsCompact K)
    (hearly : forall clock : HarnackClock, clock.origin = origin ->
      clock.time ∈ Set.Ioc origin (origin + eta) -> forall x : M,
      forall U : HamiltonHarnackTwoForm (TangentSpace I x),
      forall W : Tensor0SSpace 1 I x, (U, W) ≠ 0 ->
        0 < hamiltonPerturbedHarnackQuadraticAt (I := I) S clock
          (phi clock.time x) (psi clock.time) x U W)
    (htail : forall clock : HarnackClock, clock.origin = origin ->
      clock.time ∈ Set.Icc (origin + eta) stop -> forall x : M,
      x ∉ K -> forall U : HamiltonHarnackTwoForm (TangentSpace I x),
      forall W : Tensor0SSpace 1 I x, (U, W) ≠ 0 ->
        0 < hamiltonPerturbedHarnackQuadraticAt (I := I) S clock
          (phi clock.time x) (psi clock.time) x U W) :
    let L : Set (HarnackCarrierTotal (E := E) (I := I) (M := M)) :=
      {z | z.proj ∈ K ∧
        harnackCarrierNormSq (E := E) (I := I) (M := M) gRef z = 1}
    IsCompact L ∧
      (forall t, t ∈ Set.Ioc origin (origin + eta) -> forall x : M,
        forall z : HarnackCarrierFiber (E := E) (I := I) (M := M) x,
          0 < hamiltonPerturbedHarnackQuadraticValue
            (E := E) (I := I) (M := M) S origin phi psi t x z) ∧
      (forall t, t ∈ Set.Icc (origin + eta) stop ->
        forall z : HarnackCarrierTotal (E := E) (I := I) (M := M),
          hamiltonPerturbedHarnackQuadraticValue
              (E := E) (I := I) (M := M) S origin phi psi
                t z.proj z.2 <= 0 ->
            exists w, w ∈ L ∧
              hamiltonPerturbedHarnackQuadraticValue
                  (E := E) (I := I) (M := M) S origin phi psi
                    t w.proj w.2 <= 0 ∧
                (hamiltonPerturbedHarnackQuadraticValue
                    (E := E) (I := I) (M := M) S origin phi psi
                      t z.proj z.2 < 0 ->
                  hamiltonPerturbedHarnackQuadraticValue
                    (E := E) (I := I) (M := M) S origin phi psi
                      t w.proj w.2 < 0)) := by
  dsimp only
  let L : Set (HarnackCarrierTotal (E := E) (I := I) (M := M)) :=
    {z | z.proj ∈ K ∧
      harnackCarrierNormSq (E := E) (I := I) (M := M) gRef z = 1}
  have hL : IsCompact L := harnackCarrierNormSq_level_isCompact
    (E := E) (I := I) (M := M) gRef hK
  refine ⟨hL, ?_, ?_⟩
  · intro t ht x z
    by_cases hz : z = 0
    · subst z
      rw [hamiltonPerturbedHarnackQuadraticValue_zero]
      norm_num
    · let clock : HarnackClock := ⟨origin, t, ht.1⟩
      rw [hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
        S origin phi psi t ht.1 x z hz]
      exact hearly clock rfl ht x z.1 z.2 hz
  · intro t ht z hzq
    have horiginT : origin < t :=
      lt_of_lt_of_le (lt_add_of_pos_right origin heta) ht.1
    have hz : z.2 ≠ 0 := by
      intro hz0
      rw [hz0, hamiltonPerturbedHarnackQuadraticValue_zero] at hzq
      norm_num at hzq
    let clock : HarnackClock := ⟨origin, t, horiginT⟩
    have hzbase : z.proj ∈ K := by
      by_contra hzK
      have hQ : 0 < hamiltonPerturbedHarnackQuadraticAt (I := I) S clock
          (phi t z.proj) (psi t) z.proj z.2.1 z.2.2 :=
        htail clock rfl ht z.proj hzK z.2.1 z.2.2 hz
      have hqeq := hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
        S origin phi psi
          t horiginT z.proj z.2 hz
      exact (not_lt_of_ge hzq) (hqeq.symm ▸ hQ)
    let qnorm := harnackCarrierNormSq
      (E := E) (I := I) (M := M) gRef z
    have hqnorm : 0 < qnorm :=
      harnackCarrierNormSq_pos (E := E) (I := I) (M := M) gRef z hz
    let c := (Real.sqrt qnorm)⁻¹
    have hc : c ≠ 0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 hqnorm))
    let zn := normalizeHarnackCarrier
      (E := E) (I := I) (M := M) gRef z.proj z.2
    have hzn : zn = c • z.2 := by
      simp only [zn, normalizeHarnackCarrier, if_neg hz, c, qnorm]
    have hznne : zn ≠ 0 := by
      rw [hzn]
      exact smul_ne_zero hc hz
    let w : HarnackCarrierTotal (E := E) (I := I) (M := M) :=
      Bundle.TotalSpace.mk' (HarnackCarrierModel (E := E)) z.proj zn
    have hwnorm : harnackCarrierNormSq
        (E := E) (I := I) (M := M) gRef w = 1 := by
      exact normalizeHarnackCarrier_normSq
        (E := E) (I := I) (M := M) gRef z.proj z.2 hz
    have hwL : w ∈ L := ⟨hzbase, hwnorm⟩
    have hqz := hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
      S origin phi psi
        t horiginT z.proj z.2 hz
    have hqw := hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
      S origin phi psi
        t horiginT w.proj w.2 hznne
    have hscale :
        hamiltonPerturbedHarnackQuadraticAt (I := I) S clock
            (phi t z.proj) (psi t) z.proj zn.1 zn.2 =
          c ^ 2 * hamiltonPerturbedHarnackQuadraticAt (I := I) S clock
            (phi t z.proj) (psi t) z.proj z.2.1 z.2.2 := by
      rw [hzn]
      exact hamiltonPerturbedHarnackQuadraticAt_smul
        (I := I) S clock (phi t z.proj) (psi t) z.proj c z.2.1 z.2.2
    have hvalue : hamiltonPerturbedHarnackQuadraticValue
          (E := E) (I := I) (M := M) S origin phi psi t w.proj w.2 =
        c ^ 2 * hamiltonPerturbedHarnackQuadraticValue
          (E := E) (I := I) (M := M) S origin phi psi t z.proj z.2 := by
      rw [hqw, hqz]
      exact hscale
    refine ⟨w, hwL, ?_, ?_⟩
    · rw [hvalue]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) hzq
    · intro hstrict
      rw [hvalue]
      exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hc) hstrict

private def hamiltonCoordinateQuadratic
    {Idx : Type*} [Fintype Idx]
    {P : Type*}
    (gInv : P → Idx → Idx → Real)
    (R : P → (Fin 4 → Idx) → Real)
    (Pterm : P → (Fin 3 → Idx) → Real)
    (Mterm : P → (Fin 2 → Idx) → Real)
    (U : P → (Fin 2 → Idx) → Real)
    (W : P → (Fin 1 → Idx) → Real)
    (q : P) : Real :=
  (∑ A : Fin 4 → Idx, ∑ B : Fin 4 → Idx,
    (∏ a : Fin 4, gInv q (A a) (B a)) *
      R q (fun a => A (curvatureSlotSwap a)) *
        (U q (fun a => B (Fin.castAdd 2 a)) *
          U q (fun a => B (Fin.natAdd 2 a)))) +
  2 * (∑ A : Fin 3 → Idx, ∑ B : Fin 3 → Idx,
    (∏ a : Fin 3, gInv q (A a) (B a)) * Pterm q A *
      (U q (fun a => B (Fin.castAdd 1 a)) *
        W q (fun a => B (Fin.natAdd 2 a)))) +
  ∑ A : Fin 2 → Idx, ∑ B : Fin 2 → Idx,
    (∏ a : Fin 2, gInv q (A a) (B a)) * Mterm q A *
      (W q (fun a => B (Fin.castAdd 1 a)) *
        W q (fun a => B (Fin.natAdd 1 a)))

private theorem hamiltonCoordinateQuadratic_continuous
    {Idx : Type*} [Fintype Idx]
    {P : Type*} [TopologicalSpace P]
    (gInv : P → Idx → Idx → Real)
    (R : P → (Fin 4 → Idx) → Real)
    (Pterm : P → (Fin 3 → Idx) → Real)
    (Mterm : P → (Fin 2 → Idx) → Real)
    (U : P → (Fin 2 → Idx) → Real)
    (W : P → (Fin 1 → Idx) → Real)
    (hgInv : ∀ i j, Continuous (fun q => gInv q i j))
    (hR : ∀ slots, Continuous (fun q => R q slots))
    (hP : ∀ slots, Continuous (fun q => Pterm q slots))
    (hM : ∀ slots, Continuous (fun q => Mterm q slots))
    (hU : ∀ slots, Continuous (fun q => U q slots))
    (hW : ∀ slots, Continuous (fun q => W q slots)) :
    Continuous (hamiltonCoordinateQuadratic gInv R Pterm Mterm U W) := by
  have hInvProd {s : Nat} (A B : Fin s → Idx) : Continuous
      (fun q : P => ∏ a : Fin s, gInv q (A a) (B a)) :=
    continuous_finsetProd Finset.univ fun a _ => hgInv (A a) (B a)
  have hcurvSummand (A B : Fin 4 → Idx) : Continuous
      (fun q : P =>
        (∏ a : Fin 4, gInv q (A a) (B a)) *
          R q (fun a => A (curvatureSlotSwap a)) *
            (U q (fun a => B (Fin.castAdd 2 a)) *
              U q (fun a => B (Fin.natAdd 2 a)))) :=
    ((hInvProd A B).mul (hR (fun a => A (curvatureSlotSwap a)))).mul
      ((hU (fun a => B (Fin.castAdd 2 a))).mul
        (hU (fun a => B (Fin.natAdd 2 a))))
  have hpSummand (A B : Fin 3 → Idx) : Continuous
      (fun q : P =>
        (∏ a : Fin 3, gInv q (A a) (B a)) * Pterm q A *
          (U q (fun a => B (Fin.castAdd 1 a)) *
            W q (fun a => B (Fin.natAdd 2 a)))) :=
    ((hInvProd A B).mul (hP A)).mul
      ((hU (fun a => B (Fin.castAdd 1 a))).mul
        (hW (fun a => B (Fin.natAdd 2 a))))
  have hmSummand (A B : Fin 2 → Idx) : Continuous
      (fun q : P =>
        (∏ a : Fin 2, gInv q (A a) (B a)) * Mterm q A *
          (W q (fun a => B (Fin.castAdd 1 a)) *
            W q (fun a => B (Fin.natAdd 1 a)))) :=
    ((hInvProd A B).mul (hM A)).mul
      ((hW (fun a => B (Fin.castAdd 1 a))).mul
        (hW (fun a => B (Fin.natAdd 1 a))))
  unfold hamiltonCoordinateQuadratic
  exact ((continuous_finsetSum Finset.univ fun A _ =>
    continuous_finsetSum Finset.univ fun B _ => hcurvSummand A B).add
      (continuous_const.mul
        (continuous_finsetSum Finset.univ fun A _ =>
          continuous_finsetSum Finset.univ fun B _ => hpSummand A B))).add
    (continuous_finsetSum Finset.univ fun A _ =>
      continuous_finsetSum Finset.univ fun B _ => hmSummand A B)

private def tensorCoordinateNormSq
    {Idx : Type*} [Fintype Idx] {P : Type*} {s : Nat}
    (gInv : P → Idx → Idx → Real)
    (A : P → (Fin s → Idx) → Real) (q : P) : Real :=
  ∑ I0 : Fin s → Idx, ∑ J0 : Fin s → Idx,
    (∏ a : Fin s, gInv q (I0 a) (J0 a)) * A q I0 * A q J0

private theorem tensorCoordinateNormSq_continuous
    {Idx : Type*} [Fintype Idx] {P : Type*} [TopologicalSpace P]
    {s : Nat}
    (gInv : P → Idx → Idx → Real)
    (A : P → (Fin s → Idx) → Real)
    (hgInv : ∀ i j, Continuous (fun q => gInv q i j))
    (hA : ∀ slots, Continuous (fun q => A q slots)) :
    Continuous (tensorCoordinateNormSq gInv A) := by
  apply continuous_finsetSum
  intro I0 _
  apply continuous_finsetSum
  intro J0 _
  exact ((continuous_finsetProd Finset.univ fun a _ =>
    hgInv (I0 a) (J0 a)).mul (hA I0)).mul (hA J0)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metricFamilyNormSq_sections_continuous
    [I.Boundaryless]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {K : Set Real} (hK : K ⊆ D.regular)
    {P : Type*} [TopologicalSpace P] {s : Nat}
    (time : P → {t : Real // t ∈ K}) (htime : Continuous time)
    (b : P → M) (hb : Continuous b)
    (A : (q : P) → Tensor0SSpace s I (b q))
    (hA : Continuous
      (fun q : P => Bundle.TotalSpace.mk' (Tensor0SModel s Real E) (b q) (A q))) :
    Continuous (fun q : P => normSq0S (I := I) (G.metric (time q).1)
      (b q) s (A q)) := by
  rw [continuous_iff_continuousAt]
  intro q0
  let alpha : M := b q0
  let V : Set P := {q | b q ∈ chartLeviCivitaGoodSet (I := I) alpha}
  have hVopen : IsOpen V :=
    (chartLeviCivitaGoodSet_isOpen (I := I) alpha).preimage hb
  have hq0V : q0 ∈ V := self_mem_chartLeviCivitaGoodSet (I := I) (α := alpha)
  have hlocal : ContinuousOn
      (fun q : P => normSq0S (I := I) (G.metric (time q).1)
        (b q) s (A q)) V := by
    rw [continuousOn_iff_continuous_domRestrict]
    let Q := {q : P // q ∈ V}
    let bQ : Q → M := fun q => b q.1
    let pull : Q → {t : Real // t ∈ K} × M := fun q => (time q.1, b q.1)
    have hbQ : Continuous bQ := hb.comp continuous_subtype_val
    have hpull : Continuous pull :=
      (htime.comp continuous_subtype_val).prodMk hbQ
    have hbase (q : Q) :
        bQ q ∈ (trivializationAt E (TangentSpace I) alpha).baseSet :=
      chartLeviCivitaGoodSet_mem_baseSet (I := I) q.2
    have hslot (i : Fin (Module.finrank Real E)) : Continuous
        (fun q : Q => Bundle.TotalSpace.mk' E (bQ q)
          (chartBasisVecFiber (I := I) alpha i (bQ q))) :=
      (chartBasisVec_contMDiffOn (I := I) alpha i).continuousOn.comp_continuous
        hbQ hbase
    have hinv (i j : Fin (Module.finrank Real E)) : Continuous
        (fun q : Q => chartInvGramMatrix (I := I) (G.metric (time q.1).1)
          alpha (bQ q) i j) := by
      exact chartInvGramMatrix_family_comp_continuous
        (I := I) hG hK alpha pull hpull (fun q => q.2) i j
    have hcomp (slots : Fin s → Fin (Module.finrank Real E)) : Continuous
        (fun q : Q => A q.1
          (fun a => chartBasisVecFiber (I := I) alpha (slots a) (bQ q))) :=
      TensorMultilinear.continuous_section_apply_base
        (𝕜 := Real) (I := I) (M := M) bQ hbQ (fun q : Q => A q.1)
        (hA.comp continuous_subtype_val)
        (fun a q => chartBasisVecFiber (I := I) alpha (slots a) (bQ q))
        (fun a => hslot (slots a))
    let gInv : Q → Fin (Module.finrank Real E) →
        Fin (Module.finrank Real E) → Real := fun q i j =>
      chartInvGramMatrix (I := I) (G.metric (time q.1).1) alpha (bQ q) i j
    let Acomp : Q → (Fin s → Fin (Module.finrank Real E)) → Real :=
      fun q slots => A q.1
        (fun a => chartBasisVecFiber (I := I) alpha (slots a) (bQ q))
    have hsum : Continuous (tensorCoordinateNormSq gInv Acomp) :=
      tensorCoordinateNormSq_continuous gInv Acomp
        (fun i j => by simpa only [gInv] using hinv i j)
        (fun slots => by simpa only [Acomp] using hcomp slots)
    refine hsum.congr ?_
    intro q
    let basis := chartBasisFamily (I := I) alpha (hbase q)
    have hinverse : MetricInverseInBasis (I := I)
        (G.metric (time q.1).1) (bQ q) basis
        (fun i j => chartInvGramMatrix (I := I)
          (G.metric (time q.1).1) alpha (bQ q) i j) := by
      simpa only [basis] using chartInvGram_inverse
        (I := I) (G.metric (time q.1).1) alpha (hbase q)
    change tensorCoordinateNormSq gInv Acomp q =
      normSq0S (I := I) (G.metric (time q.1).1) (bQ q) s (A q.1)
    symm
    rw [normSq0S_eq_coord (I := I) (G.metric (time q.1).1)
      (bQ q) s basis _ hinverse]
    unfold coordInner0S tensorCoordinateNormSq tensor0SComponent gInv Acomp
    simp only [basis, chartBasisFamily_apply]
  exact hlocal.continuousAt (hVopen.mem_nhds hq0V)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonCoordinateQuadratic_sections_continuous
    {P : Type*} [TopologicalSpace P]
    (b : P → M) (hb : Continuous b)
    (v : Fin (Module.finrank Real E) →
      (q : P) → TangentSpace I (b q))
    (hv : ∀ i, Continuous
      (fun q : P => Bundle.TotalSpace.mk' E (b q) (v i q)))
    (gInv : P → Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → Real)
    (hgInv : ∀ i j, Continuous (fun q => gInv q i j))
    (R : (q : P) → Tensor0SSpace 4 I (b q))
    (hR : Continuous
      (fun q : P => Bundle.TotalSpace.mk' (Tensor0SModel 4 Real E) (b q) (R q)))
    (Pterm : (q : P) → Tensor0SSpace 3 I (b q))
    (hP : Continuous
      (fun q : P => Bundle.TotalSpace.mk' (Tensor0SModel 3 Real E) (b q) (Pterm q)))
    (Mterm : (q : P) → Tensor0SSpace 2 I (b q))
    (hM : Continuous
      (fun q : P => Bundle.TotalSpace.mk' (Tensor0SModel 2 Real E) (b q) (Mterm q)))
    (U : (q : P) → Tensor0SSpace 2 I (b q))
    (hU : Continuous
      (fun q : P => Bundle.TotalSpace.mk' (Tensor0SModel 2 Real E) (b q) (U q)))
    (W : (q : P) → Tensor0SSpace 1 I (b q))
    (hW : Continuous
      (fun q : P => Bundle.TotalSpace.mk' (Tensor0SModel 1 Real E) (b q) (W q))) :
    Continuous
      (hamiltonCoordinateQuadratic gInv
        (fun q slots => R q (fun a => v (slots a) q))
        (fun q slots => Pterm q (fun a => v (slots a) q))
        (fun q slots => Mterm q (fun a => v (slots a) q))
        (fun q slots => U q (fun a => v (slots a) q))
        (fun q slots => W q (fun a => v (slots a) q))) := by
  have hRcomp (slots : Fin 4 → Fin (Module.finrank Real E)) : Continuous
      (fun q : P => R q (fun a => v (slots a) q)) :=
    TensorMultilinear.continuous_section_apply_base
      (𝕜 := Real) (I := I) (M := M) b hb R hR
      (fun a q => v (slots a) q) (fun a => hv (slots a))
  have hPcomp (slots : Fin 3 → Fin (Module.finrank Real E)) : Continuous
      (fun q : P => Pterm q (fun a => v (slots a) q)) :=
    TensorMultilinear.continuous_section_apply_base
      (𝕜 := Real) (I := I) (M := M) b hb Pterm hP
      (fun a q => v (slots a) q) (fun a => hv (slots a))
  have hMcomp (slots : Fin 2 → Fin (Module.finrank Real E)) : Continuous
      (fun q : P => Mterm q (fun a => v (slots a) q)) :=
    TensorMultilinear.continuous_section_apply_base
      (𝕜 := Real) (I := I) (M := M) b hb Mterm hM
      (fun a q => v (slots a) q) (fun a => hv (slots a))
  have hUcomp (slots : Fin 2 → Fin (Module.finrank Real E)) : Continuous
      (fun q : P => U q (fun a => v (slots a) q)) :=
    TensorMultilinear.continuous_section_apply_base
      (𝕜 := Real) (I := I) (M := M) b hb U hU
      (fun a q => v (slots a) q) (fun a => hv (slots a))
  have hWcomp (slots : Fin 1 → Fin (Module.finrank Real E)) : Continuous
      (fun q : P => W q (fun a => v (slots a) q)) :=
    TensorMultilinear.continuous_section_apply_base
      (𝕜 := Real) (I := I) (M := M) b hb W hW
      (fun a q => v (slots a) q) (fun a => hv (slots a))
  exact hamiltonCoordinateQuadratic_continuous _ _ _ _ _ _ hgInv
    hRcomp hPcomp hMcomp hUcomp hWcomp

omit [SigmaCompactSpace M] in
theorem hamiltonHarnackQuadratic_continuous [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (origin : Real) {K : Set Real}
    (hK : K ⊆ D.regular) (horigin : ∀ t ∈ K, origin < t) :
    Continuous
      (fun q : {t : Real // t ∈ K} ×
          HarnackCarrierTotal (E := E) (I := I) (M := M) =>
        hamiltonHarnackQuadraticAt (I := I) S
          ⟨origin, q.1.1, horigin q.1.1 q.1.2⟩
          q.2.proj q.2.2.1 q.2.2.2) := by
  classical
  let P := {t : Real // t ∈ K} ×
    HarnackCarrierTotal (E := E) (I := I) (M := M)
  have hbaseP : Continuous (fun q : P => q.2.proj) :=
    (FiberBundle.continuous_proj (HarnackCarrierModel (E := E))
      (HarnackCarrierFiber (E := E) (I := I) (M := M))).comp continuous_snd
  have hKcarrier : K ⊆ D.carrier := fun _ ht => D.regular_subset (hK ht)
  have hrmFamily := hS.rm04Cont.mono hKcarrier
  have hpFamily := hamiltonPAt_family_continuous (I := I) S hS hK
  have hmFamily := hamiltonMAt_origin_family_continuous
    (I := I) S hS origin hK horigin
  rw [continuous_iff_continuousAt]
  intro q0
  let alpha : M := q0.2.proj
  let V : Set P :=
    {q | q.2.proj ∈ chartLeviCivitaGoodSet (I := I) alpha}
  have hVopen : IsOpen V :=
    (chartLeviCivitaGoodSet_isOpen (I := I) alpha).preimage hbaseP
  have hq0V : q0 ∈ V := by
    exact self_mem_chartLeviCivitaGoodSet (I := I) (α := alpha)
  have hlocal : ContinuousOn
      (fun q : P =>
        hamiltonHarnackQuadraticAt (I := I) S
          ⟨origin, q.1.1, horigin q.1.1 q.1.2⟩
          q.2.proj q.2.2.1 q.2.2.2) V := by
    rw [continuousOn_iff_continuous_domRestrict]
    let Q := {q : P // q ∈ V}
    let b : Q → M := fun q => q.1.2.proj
    have hb : Continuous b := hbaseP.comp continuous_subtype_val
    let pull : Q → {t : Real // t ∈ K} × M :=
      fun q => (q.1.1, q.1.2.proj)
    have hpull : Continuous pull :=
      (continuous_fst.comp continuous_subtype_val).prodMk hb
    have hbase (q : Q) :
        b q ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
      exact chartLeviCivitaGoodSet_mem_baseSet (I := I) q.2
    have hslot (i : Fin (Module.finrank Real E)) : Continuous
        (fun q : Q => Bundle.TotalSpace.mk' E (b q)
          (chartBasisVecFiber (I := I) alpha i (b q))) := by
      exact (chartBasisVec_contMDiffOn (I := I) alpha i).continuousOn.comp_continuous
        hb hbase
    have hrmTotal : Continuous
        (fun q : Q => Bundle.TotalSpace.mk' (Tensor0SModel 4 Real E) (b q)
          (S.base.rm04 q.1.1.1 (b q))) := by
      unfold tensor0SFamilyContinuousOnSet at hrmFamily
      exact hrmFamily.comp hpull
    have hpTotal : Continuous
        (fun q : Q => Bundle.TotalSpace.mk' (Tensor0SModel 3 Real E) (b q)
          (hamiltonPAt (I := I) (S.base.metric q.1.1.1) (b q))) := by
      unfold tensor0SFamilyContinuousOnSet at hpFamily
      change Continuous
        ((fun q : {t : Real // t ∈ K} × M =>
          Bundle.TotalSpace.mk' (Tensor0SModel 3 Real E) q.2
            (hamiltonPAt (I := I) (S.base.metric q.1.1) q.2)) ∘ pull)
      simpa only [SolutionOn.family_metric] using hpFamily.comp hpull
    have hmTotal : Continuous
        (fun q : Q => Bundle.TotalSpace.mk' (Tensor0SModel 2 Real E) (b q)
          (hamiltonMbarAt (I := I) (S.base.metric q.1.1.1) (b q) +
            (1 / (2 * (q.1.1.1 - origin)) : Real) •
              metricRicci (I := I) (M := M)
                (S.base.metric q.1.1.1) (b q))) := by
      unfold tensor0SFamilyContinuousOnSet at hmFamily
      change Continuous
        ((fun q : {t : Real // t ∈ K} × M =>
          Bundle.TotalSpace.mk' (Tensor0SModel 2 Real E) q.2
            (hamiltonMbarAt (I := I) (S.base.metric q.1.1) q.2 +
              (1 / (2 * (q.1.1 - origin)) : Real) •
                metricRicci (I := I) (M := M)
                  (S.base.metric q.1.1) q.2)) ∘ pull)
      simpa only [SolutionOn.family_metric] using hmFamily.comp hpull
    have huTotal : Continuous
        (fun q : Q => Bundle.TotalSpace.mk' (Tensor0SModel 2 Real E) (b q)
          (HamiltonHarnackTwoForm.toTensor0S (I := I) q.1.2.2.1)) := by
      exact (harnackTwoFormToTensorTotal_continuous.comp
        harnackCarrier_first_continuous).comp
          (continuous_snd.comp continuous_subtype_val)
    have hwTotal : Continuous
        (fun q : Q => Bundle.TotalSpace.mk' (Tensor0SModel 1 Real E) (b q)
          q.1.2.2.2) := by
      exact harnackCarrier_second_continuous.comp
        (continuous_snd.comp continuous_subtype_val)
    have hinv (i j : Fin (Module.finrank Real E)) : Continuous
        (fun q : Q =>
          (chartInvGramMatrix (I := I) (S.base.metric q.1.1.1)
            alpha (b q)) i j) := by
      have hraw := chartInvGramMatrix_family_comp_continuous
        (I := I) (G := S.family) hS.smoothMetric hK alpha pull hpull
        (fun q => q.2) i j
      simpa only [pull, b, SolutionOn.family_metric] using hraw
    let gInv : Q → Fin (Module.finrank Real E) →
        Fin (Module.finrank Real E) → Real := fun q i j =>
      (chartInvGramMatrix (I := I) (S.base.metric q.1.1.1)
        alpha (b q)) i j
    let Rcomp : Q → (Fin 4 → Fin (Module.finrank Real E)) → Real := fun q slots =>
      S.base.rm04 q.1.1.1 (b q)
        (fun a => chartBasisVecFiber (I := I) alpha (slots a) (b q))
    let Pcomp : Q → (Fin 3 → Fin (Module.finrank Real E)) → Real := fun q slots =>
      hamiltonPAt (I := I) (S.base.metric q.1.1.1) (b q)
        (fun a => chartBasisVecFiber (I := I) alpha (slots a) (b q))
    let Mcomp : Q → (Fin 2 → Fin (Module.finrank Real E)) → Real := fun q slots =>
      (hamiltonMbarAt (I := I) (S.base.metric q.1.1.1) (b q) +
        (1 / (2 * (q.1.1.1 - origin)) : Real) •
          metricRicci (I := I) (M := M) (S.base.metric q.1.1.1) (b q))
        (fun a => chartBasisVecFiber (I := I) alpha (slots a) (b q))
    let Ucomp : Q → (Fin 2 → Fin (Module.finrank Real E)) → Real := fun q slots =>
      HamiltonHarnackTwoForm.toTensor0S (I := I) q.1.2.2.1
        (fun a => chartBasisVecFiber (I := I) alpha (slots a) (b q))
    let Wcomp : Q → (Fin 1 → Fin (Module.finrank Real E)) → Real := fun q slots =>
      q.1.2.2.2 (fun a => chartBasisVecFiber (I := I) alpha (slots a) (b q))
    have hsum : Continuous
        (hamiltonCoordinateQuadratic gInv Rcomp Pcomp Mcomp Ucomp Wcomp) :=
      hamiltonCoordinateQuadratic_sections_continuous
        (I := I) (M := M) b hb
        (fun i q => chartBasisVecFiber (I := I) alpha i (b q)) hslot
        gInv (fun i j => by simpa only [gInv] using hinv i j)
        (fun q => S.base.rm04 q.1.1.1 (b q)) hrmTotal
        (fun q => hamiltonPAt (I := I)
          (S.base.metric q.1.1.1) (b q)) hpTotal
        (fun q => hamiltonMbarAt (I := I) (S.base.metric q.1.1.1) (b q) +
          (1 / (2 * (q.1.1.1 - origin)) : Real) •
            metricRicci (I := I) (M := M)
              (S.base.metric q.1.1.1) (b q)) hmTotal
        (fun q => HamiltonHarnackTwoForm.toTensor0S (I := I) q.1.2.2.1) huTotal
        (fun q => q.1.2.2.2) hwTotal
    refine hsum.congr ?_
    intro q
    have hxbase : b q ∈ (trivializationAt E (TangentSpace I) alpha).baseSet :=
      hbase q
    let basis := chartBasisFamily (I := I) alpha hxbase
    have hinverse : MetricInverseInBasis (I := I)
        (S.base.metric q.1.1.1) (b q) basis
        (fun i j => (chartInvGramMatrix (I := I)
          (S.base.metric q.1.1.1) alpha (b q)) i j) := by
      simpa only [basis] using chartInvGram_inverse
        (I := I) (S.base.metric q.1.1.1) alpha hxbase
    let clock : HarnackClock :=
      ⟨origin, q.1.1.1, horigin q.1.1.1 q.1.1.2⟩
    have hM :
        hamiltonMbarAt (I := I) (S.base.metric q.1.1.1) (b q) +
            (1 / (2 * (q.1.1.1 - origin)) : Real) •
              metricRicci (I := I) (M := M)
                (S.base.metric q.1.1.1) (b q) =
          hamiltonMAt (I := I) clock
            (S.base.metric q.1.1.1) (b q) := by
      simp [hamiltonMAt, clock, HarnackClock.elapsed]
    symm
    change hamiltonHarnackQuadraticAt (I := I) S clock
      (b q) q.1.2.2.1 q.1.2.2.2 = _
    dsimp only [clock]
    rw [hamiltonHarnackQuadraticAt, hamiltonQuadraticAt, curvatureBlock]
    rw [inner0S_eq_coord (I := I) (S.base.metric q.1.1.1)
      (b q) 4 basis _ hinverse]
    rw [inner0S_eq_coord (I := I) (S.base.metric q.1.1.1)
      (b q) 3 basis _ hinverse]
    rw [inner0S_eq_coord (I := I) (S.base.metric q.1.1.1)
      (b q) 2 basis _ hinverse]
    rw [← hM]
    have hUprod (B : Fin 4 → Fin (Module.finrank Real E)) :
        (HamiltonHarnackTwoForm.toTensor0S (I := I) q.1.2.2.1).product
            (HamiltonHarnackTwoForm.toTensor0S (I := I) q.1.2.2.1)
            (fun a => basis (B a)) =
          q.1.2.2.1 (fun a => basis (B (Fin.castAdd 2 a))) *
            q.1.2.2.1 (fun a => basis (B (Fin.natAdd 2 a))) := by
      rw [Tensor0SSpace.product_apply,
        HamiltonHarnackTwoForm.toTensor0S_apply,
        HamiltonHarnackTwoForm.toTensor0S_apply]
      rfl
    have hPprod (B : Fin 3 → Fin (Module.finrank Real E)) :
        (HamiltonHarnackTwoForm.toTensor0S (I := I) q.1.2.2.1).product
            q.1.2.2.2 (fun a => basis (B a)) =
          q.1.2.2.1 (fun a => basis (B (Fin.castAdd 1 a))) *
            q.1.2.2.2 (fun a => basis (B (Fin.natAdd 2 a))) := by
      rw [Tensor0SSpace.product_apply,
        HamiltonHarnackTwoForm.toTensor0S_apply]
      rfl
    have hWprod (B : Fin 2 → Fin (Module.finrank Real E)) :
        q.1.2.2.2.product q.1.2.2.2 (fun a => basis (B a)) =
          q.1.2.2.2 (fun a => basis (B (Fin.castAdd 1 a))) *
            q.1.2.2.2 (fun a => basis (B (Fin.natAdd 1 a))) := by
      rw [Tensor0SSpace.product_apply]
      rfl
    unfold hamiltonCoordinateQuadratic gInv Rcomp Pcomp Mcomp Ucomp Wcomp
    unfold coordInner0S tensor0SComponent
    simp_rw [hUprod, hPprod, hWprod]
    simp only [Tensor0SSpace.domDomCongr_apply,
      HamiltonHarnackTwoForm.toTensor0S_apply, basis, chartBasisFamily_apply]
  exact hlocal.continuousAt (hVopen.mem_nhds hq0V)

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackQuadratic_continuous [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (origin : Real) {K : Set Real}
    (hK : K ⊆ D.regular) (horigin : ∀ t ∈ K, origin < t)
    (phi : Real → M → Real) (psi : Real → Real)
    (hphi : Continuous (fun q : {t : Real // t ∈ K} × M =>
      phi q.1.1 q.2))
    (hpsi : Continuous (fun t : {t : Real // t ∈ K} => psi t.1)) :
    Continuous
      (fun q : {t : Real // t ∈ K} ×
          HarnackCarrierTotal (E := E) (I := I) (M := M) =>
        hamiltonPerturbedHarnackQuadraticAt (I := I) S
          ⟨origin, q.1.1, horigin q.1.1 q.1.2⟩
          (phi q.1.1 q.2.proj) (psi q.1.1)
          q.2.proj q.2.2.1 q.2.2.2) := by
  let P := {t : Real // t ∈ K} ×
    HarnackCarrierTotal (E := E) (I := I) (M := M)
  have hbase : Continuous (fun q : P => q.2.proj) :=
    (FiberBundle.continuous_proj (HarnackCarrierModel (E := E))
      (HarnackCarrierFiber (E := E) (I := I) (M := M))).comp continuous_snd
  have hpull : Continuous (fun q : P => (q.1, q.2.proj)) :=
    continuous_fst.prodMk hbase
  have hQ : Continuous
      (fun q : P => hamiltonHarnackQuadraticAt (I := I) S
        ⟨origin, q.1.1, horigin q.1.1 q.1.2⟩
        q.2.proj q.2.2.1 q.2.2.2) :=
    hamiltonHarnackQuadratic_continuous (I := I) S hS origin hK horigin
  have hW : Continuous (fun q : P =>
      normSq0S (I := I) (S.base.metric q.1.1) q.2.proj 1 q.2.2.2) := by
    simpa only [SolutionOn.family_metric] using
      metricFamilyNormSq_sections_continuous
        (I := I) (G := S.family) hS.smoothMetric hK
        (fun q : P => q.1) continuous_fst
        (fun q : P => q.2.proj) hbase (fun q : P => q.2.2.2)
        (harnackCarrier_second_continuous.comp continuous_snd)
  have hU : Continuous (fun q : P =>
      normSq0S (I := I) (S.base.metric q.1.1) q.2.proj 2 q.2.2.1.toTensor0S) := by
    simpa only [SolutionOn.family_metric] using
      metricFamilyNormSq_sections_continuous
        (I := I) (G := S.family) hS.smoothMetric hK
        (fun q : P => q.1) continuous_fst
        (fun q : P => q.2.proj) hbase
        (fun q : P => q.2.2.1.toTensor0S)
        (harnackTwoFormToTensorTotal_continuous.comp
          (harnackCarrier_first_continuous.comp continuous_snd))
  have hphiP : Continuous (fun q : P => phi q.1.1 q.2.proj) :=
    hphi.comp hpull
  have hpsiP : Continuous (fun q : P => psi q.1.1) :=
    hpsi.comp continuous_fst
  have helapsed : Continuous (fun q : P => q.1.1 - origin) :=
    (continuous_subtype_val.comp continuous_fst).sub continuous_const
  have hne : ∀ q : P, q.1.1 - origin ≠ 0 := by
    intro q hzero
    have := horigin q.1.1 q.1.2
    linarith
  have hfrac : Continuous (fun q : P => phi q.1.1 q.2.proj / (q.1.1 - origin)) :=
    hphiP.div helapsed hne
  have htotal := (hQ.add (hfrac.mul hW)).add (hpsiP.mul hU)
  change Continuous (fun q : P =>
    hamiltonHarnackQuadraticAt (I := I) S
        ⟨origin, q.1.1, horigin q.1.1 q.1.2⟩
        q.2.proj q.2.2.1 q.2.2.2 +
      phi q.1.1 q.2.proj / (q.1.1 - origin) *
        normSq0S (I := I) (S.base.metric q.1.1) q.2.proj 1 q.2.2.2 +
      psi q.1.1 * normSq0S (I := I) (S.base.metric q.1.1)
        q.2.proj 2 q.2.2.1.toTensor0S)
  exact htotal.congr fun _ => rfl

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackRayleigh_continuousOn_level
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (origin : Real) {K : Set Real}
    (hK : K ⊆ D.regular) (horigin : ∀ t ∈ K, origin < t)
    (phi : Real → M → Real) (psi : Real → Real)
    (hphi : Continuous (fun q : {t : Real // t ∈ K} × M =>
      phi q.1.1 q.2))
    (hpsi : Continuous (fun t : {t : Real // t ∈ K} => psi t.1))
    (gRef : SmoothRiemannianMetric I M) (C : Set M) :
    ContinuousOn
      (fun q : {t : Real // t ∈ K} ×
          HarnackCarrierTotal (E := E) (I := I) (M := M) =>
        hamiltonPerturbedHarnackRayleigh (E := E) (I := I) (M := M)
          S origin phi psi gRef q.1.1 q.2.proj q.2.2)
      {q | q.2.proj ∈ C ∧
        harnackCarrierNormSq (E := E) (I := I) (M := M) gRef q.2 = 1} := by
  refine (hamiltonPerturbedHarnackQuadratic_continuous
    (I := I) S hS origin hK horigin phi psi hphi hpsi).continuousOn.congr ?_
  intro q hq
  have hlevel :
      harnackCarrierNormSq (E := E) (I := I) (M := M) gRef q.2 = 1 := hq.2
  have hz : q.2.2 ≠ 0 := by
    intro hz
    have hzero : harnackCarrierNormSq (E := E) (I := I) (M := M) gRef q.2 = 0 := by
      have hsmul := harnackCarrierNormSq_smul
        (E := E) (I := I) (M := M) gRef q.2.proj 0 q.2.2
      rw [show q.2 = Bundle.TotalSpace.mk'
          (HarnackCarrierModel (E := E)) q.2.proj 0 by
        refine Bundle.TotalSpace.ext rfl ?_
        exact heq_of_eq hz]
      simpa using hsmul
    rw [hzero] at hlevel
    norm_num at hlevel
  classical
  simp only [hamiltonPerturbedHarnackRayleigh,
    dif_pos (horigin q.1.1 q.1.2)]
  rw [if_neg hz, hlevel, div_one]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonBarrierPhi_continuous
    {K : Set Real} (epsilon A origin : Real) (h : M -> Real)
    (hh : Continuous h) :
    Continuous (fun q : {t : Real // t ∈ K} × M =>
      hamiltonBarrierPhi epsilon A origin h q.1.1 q.2) := by
  have htime : Continuous (fun q : {t : Real // t ∈ K} × M =>
      q.1.1 - origin) :=
    (continuous_subtype_val.comp continuous_fst).sub continuous_const
  exact (continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul htime))).mul
      (hh.comp continuous_snd)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem hamiltonBarrierPsi_continuous
    {K : Set Real} (kappa epsilon B origin : Real) :
    Continuous (fun t : {t : Real // t ∈ K} =>
      hamiltonBarrierPsi kappa epsilon B origin t.1) := by
  have htime : Continuous (fun t : {t : Real // t ∈ K} =>
      t.1 - origin) := continuous_subtype_val.sub continuous_const
  exact continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul htime))

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackRayleigh_continuousOn_compact_level
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (origin : Real) {T : Set Real}
    (hTD : T ⊆ D.regular) (horigin : forall t, t ∈ T -> origin < t)
    (phi : Real -> M -> Real) (psi : Real -> Real)
    (hphi : Continuous (fun q : {t : Real // t ∈ T} × M =>
      phi q.1.1 q.2))
    (hpsi : Continuous (fun t : {t : Real // t ∈ T} => psi t.1))
    (gRef : SmoothRiemannianMetric I M) (C : Set M) :
    ContinuousOn
      (fun q : Real × HarnackCarrierTotal (E := E) (I := I) (M := M) =>
        hamiltonPerturbedHarnackRayleigh (E := E) (I := I) (M := M)
          S origin phi psi gRef q.1 q.2.proj q.2.2)
      (T ×ˢ {z : HarnackCarrierTotal (E := E) (I := I) (M := M) |
        z.proj ∈ C ∧
          harnackCarrierNormSq (E := E) (I := I) (M := M) gRef z = 1}) := by
  let L : Set (HarnackCarrierTotal (E := E) (I := I) (M := M)) :=
    {z | z.proj ∈ C ∧
      harnackCarrierNormSq (E := E) (I := I) (M := M) gRef z = 1}
  rw [continuousOn_iff_continuous_domRestrict]
  let P := {q : Real × HarnackCarrierTotal (E := E) (I := I) (M := M) //
    q ∈ T ×ˢ L}
  let pull : P -> {t : Real // t ∈ T} ×
      HarnackCarrierTotal (E := E) (I := I) (M := M) :=
    fun q => (⟨q.1.1, q.2.1⟩, q.1.2)
  have hpull : Continuous pull := by
    exact (continuous_fst.comp continuous_subtype_val).subtype_mk
      (fun q => q.2.1) |>.prodMk
        (continuous_snd.comp continuous_subtype_val)
  have hpullLevel : forall q : P,
      (pull q).2.proj ∈ C ∧
        harnackCarrierNormSq (E := E) (I := I) (M := M) gRef
          (pull q).2 = 1 := by
    intro q
    exact q.2.2
  have hcont := hamiltonPerturbedHarnackRayleigh_continuousOn_level
    (I := I) S hS origin hTD horigin phi psi hphi hpsi gRef C
  have hcomp := hcont.comp_continuous hpull hpullLevel
  change Continuous (fun q : P =>
    hamiltonPerturbedHarnackRayleigh (E := E) (I := I) (M := M)
      S origin phi psi gRef q.1.1 q.1.2.proj q.1.2.2)
  refine hcomp.congr ?_
  intro q
  rfl

omit [SigmaCompactSpace M] in
private theorem hamiltonPerturbedHarnackQuadraticValue_continuousOn_compact_level
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (origin : Real) {T : Set Real}
    (hTD : T ⊆ D.regular) (horigin : forall t, t ∈ T -> origin < t)
    (phi : Real -> M -> Real) (psi : Real -> Real)
    (hphi : Continuous (fun q : {t : Real // t ∈ T} × M =>
      phi q.1.1 q.2))
    (hpsi : Continuous (fun t : {t : Real // t ∈ T} => psi t.1))
    (gRef : SmoothRiemannianMetric I M) (C : Set M) :
    ContinuousOn
      (fun q : Real × HarnackCarrierTotal (E := E) (I := I) (M := M) =>
        hamiltonPerturbedHarnackQuadraticValue
          (E := E) (I := I) (M := M) S origin phi psi
            q.1 q.2.proj q.2.2)
      (T ×ˢ {z : HarnackCarrierTotal (E := E) (I := I) (M := M) |
        z.proj ∈ C ∧
          harnackCarrierNormSq (E := E) (I := I) (M := M) gRef z = 1}) := by
  have hcont := hamiltonPerturbedHarnackRayleigh_continuousOn_compact_level
    (I := I) S hS origin hTD horigin phi psi hphi hpsi gRef C
  refine hcont.congr ?_
  intro q hq
  have hlevel :
      harnackCarrierNormSq (E := E) (I := I) (M := M) gRef q.2 = 1 := hq.2.2
  have hz : q.2.2 ≠ 0 := by
    intro hz
    have hzero : harnackCarrierNormSq
        (E := E) (I := I) (M := M) gRef q.2 = 0 := by
      have hsmul := harnackCarrierNormSq_smul
        (E := E) (I := I) (M := M) gRef q.2.proj 0 q.2.2
      rw [show q.2 = Bundle.TotalSpace.mk'
          (HarnackCarrierModel (E := E)) q.2.proj 0 by
        refine Bundle.TotalSpace.ext rfl ?_
        exact heq_of_eq hz]
      simpa using hsmul
    rw [hzero] at hlevel
    norm_num at hlevel
  change hamiltonPerturbedHarnackQuadraticValue
      (E := E) (I := I) (M := M) S origin phi psi q.1 q.2.proj q.2.2 =
    hamiltonPerturbedHarnackRayleigh
      (E := E) (I := I) (M := M) S origin phi psi gRef q.1 q.2.proj q.2.2
  rw [hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
    S origin phi psi q.1 (horigin q.1 hq.1) q.2.proj q.2.2 hz]
  classical
  simp only [hamiltonPerturbedHarnackRayleigh,
    dif_pos (horigin q.1 hq.1), if_neg hz, hlevel, div_one]

private theorem exists_hamiltonPerturbedHarnackQuadraticAt_pos_on_connected_slab
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alphaMinus origin stop C : Real}
    (hbuffer : alphaMinus < origin)
    (horiginStop : origin < stop)
    (hslab : Set.Icc alphaMinus stop ⊆ D.carrier)
    (hreg : Set.Ioc alphaMinus stop ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete
      (I := I) (S.base.metric alphaMinus))
    (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Set.Icc alphaMinus stop, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ Set.Icc origin stop, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ h : M → Real, ∃ barrierA barrierB kappa epsilon0 : Real,
      0 < epsilon0 ∧ ∀ epsilon ∈ Set.Ioc (0 : Real) epsilon0,
          ∀ t, ∀ ht : t ∈ Set.Ioc origin stop, ∀ x : M,
            ∀ U : HamiltonHarnackTwoForm (TangentSpace I x),
            ∀ W : Tensor0SSpace 1 I x, (U, W) ≠ 0 →
              0 < hamiltonPerturbedHarnackQuadraticAt (I := I) S
                ⟨origin, t, ht.1⟩
                (hamiltonBarrierPhi epsilon barrierA origin h t x)
                (hamiltonBarrierPsi kappa epsilon barrierB origin t) x U W := by
  obtain ⟨reactionK, reactionB, reactionC, hreactionK, _hreactionB,
      hreactionC, hReactionB, hReactionCphi, hReactionCpsiW,
      hReactionCpsiU, hderiv⟩ :=
    exists_hamiltonPerturbedBlock_slab_control
      (I := I) S hS hbuffer horiginStop.le hslab hreg hcomplete hC hcurv
  have hsec : ∀ x : M, metricRm04At (I := I) (S.base.metric origin) x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M) := by
    intro x
    exact algebraicCurvatureOperatorNonnegativeCone_le_sectionalNonnegativeCone
      (hR origin ⟨le_rfl, horiginStop.le⟩ x)
  obtain ⟨h, hcont, hproper, hh, Ch, hCh, hsupport⟩ :=
    exists_proper_exhaustion_with_gradient_laplacian_bound_on_slab
      (I := I) S hS hbuffer horiginStop hslab hreg hcomplete hC hcurv hsec
  obtain ⟨barrierA, barrierB, kappa, hkappa, hCA, hCB, hsmall⟩ :=
    exists_hamilton_barrier_parameters
      (S := stop - origin) hreactionC (zero_le_one.trans hCh)
  have hbarrierA : 0 ≤ barrierA := by linarith
  have hbarrierB : 0 ≤ barrierB := by linarith
  let epsilon0 :=
    (kappa * Real.exp (barrierB * (stop - origin)))⁻¹
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    positivity
  refine ⟨h, barrierA, barrierB, kappa, epsilon0, hepsilon0, ?_⟩
  intro epsilon hepsilon
  have hpsi1 : ∀ t ∈ Set.Ioc origin stop,
      hamiltonBarrierPsi kappa epsilon barrierB origin t ≤ 1 := by
    intro t ht
    have hexp : Real.exp (barrierB * (t - origin)) ≤
        Real.exp (barrierB * (stop - origin)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 origin) hbarrierB
    have hfactor : 0 ≤ kappa * epsilon :=
      (mul_pos hkappa hepsilon.1).le
    calc
      hamiltonBarrierPsi kappa epsilon barrierB origin t =
          kappa * epsilon * Real.exp (barrierB * (t - origin)) := rfl
      _ ≤ kappa * epsilon * Real.exp (barrierB * (stop - origin)) :=
        mul_le_mul_of_nonneg_left hexp hfactor
      _ ≤ kappa * epsilon0 * Real.exp (barrierB * (stop - origin)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hepsilon.2 hkappa.le)
          (Real.exp_nonneg _)
      _ = 1 := by
        dsimp only [epsilon0]
        field_simp
  obtain ⟨eta, K, heta, hetaStop, hK, hearly, htail⟩ :=
    exists_hamiltonPerturbedHarnackQuadratic_barrier_localization
      (I := I) S hS hbuffer horiginStop hslab hreg hcomplete hC hcurv hR
      hbarrierA hbarrierB hkappa hepsilon.1 h hproper hh
  let phi : Real → M → Real :=
    hamiltonBarrierPhi epsilon barrierA origin h
  let psi : Real → Real :=
    hamiltonBarrierPsi kappa epsilon barrierB origin
  let gRef : SmoothRiemannianMetric I M := S.base.metric origin
  let L : Set (HarnackCarrierTotal (E := E) (I := I) (M := M)) :=
    {z | z.proj ∈ K ∧
      harnackCarrierNormSq (E := E) (I := I) (M := M) gRef z = 1}
  have hrepresentatives :=
    hamiltonPerturbedHarnackQuadraticValue_compact_representatives
      (E := E) (I := I) (M := M) S origin stop eta phi psi gRef K
      heta hK (by simpa only [phi, psi] using hearly)
        (by simpa only [phi, psi] using htail)
  have hL : IsCompact L := by
    simpa only [L] using hrepresentatives.1
  have hearlyValue : ∀ t, t ∈ Set.Ioc origin (origin + eta) →
      ∀ x : M, ∀ z : HarnackCarrierFiber (E := E) (I := I) (M := M) x,
        0 < hamiltonPerturbedHarnackQuadraticValue
          (E := E) (I := I) (M := M) S origin phi psi t x z := by
    simpa only [L] using hrepresentatives.2.1
  have hrepresent : ∀ t, t ∈ Set.Icc (origin + eta) stop →
      ∀ z : HarnackCarrierTotal (E := E) (I := I) (M := M),
        hamiltonPerturbedHarnackQuadraticValue
            (E := E) (I := I) (M := M) S origin phi psi
              t z.proj z.2 ≤ 0 →
          ∃ w, w ∈ L ∧
            hamiltonPerturbedHarnackQuadraticValue
                (E := E) (I := I) (M := M) S origin phi psi
                  t w.proj w.2 ≤ 0 ∧
              (hamiltonPerturbedHarnackQuadraticValue
                    (E := E) (I := I) (M := M) S origin phi psi
                      t z.proj z.2 < 0 →
                hamiltonPerturbedHarnackQuadraticValue
                    (E := E) (I := I) (M := M) S origin phi psi
                      t w.proj w.2 < 0) := by
    simpa only [L] using hrepresentatives.2.2
  have htimeReg : Set.Icc (origin + eta) stop ⊆ D.regular := by
    intro t ht
    apply hreg
    constructor
    · exact hbuffer.trans
        ((lt_add_of_pos_right origin heta).trans_le ht.1)
    · exact ht.2
  have hregOrigin : Set.Ioc origin stop ⊆ D.regular := by
    intro t ht
    exact hreg ⟨hbuffer.trans ht.1, ht.2⟩
  have horiginTime : ∀ t ∈ Set.Icc (origin + eta) stop, origin < t := by
    intro t ht
    exact (lt_add_of_pos_right origin heta).trans_le ht.1
  have hphiContinuous : Continuous
      (fun q : {t : Real // t ∈ Set.Icc (origin + eta) stop} × M =>
        phi q.1.1 q.2) := by
    simpa only [phi] using hamiltonBarrierPhi_continuous
      epsilon barrierA origin h hcont
  have hpsiContinuous : Continuous
      (fun t : {t : Real // t ∈ Set.Icc (origin + eta) stop} => psi t.1) := by
    simpa only [psi] using hamiltonBarrierPsi_continuous
      kappa epsilon barrierB origin
  have hcontinuous : ContinuousOn
      (fun q : Real × HarnackCarrierTotal (E := E) (I := I) (M := M) =>
        hamiltonPerturbedHarnackQuadraticValue
          (E := E) (I := I) (M := M) S origin phi psi
            q.1 q.2.proj q.2.2)
      (Set.Icc (origin + eta) stop ×ˢ L) := by
    simpa only [L] using
      hamiltonPerturbedHarnackQuadraticValue_continuousOn_compact_level
        (E := E) (I := I) (M := M) S hS origin htimeReg horiginTime
          phi psi hphiContinuous hpsiContinuous gRef K
  have hmetricCompatible : ∀ t,
      IsMetricCompatible (I := I)
        (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t) := by
    intro t
    simpa only [LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible
        (I := I) (S.base.metric t))
  have hstrictSupport : ∀ t, t ∈ Set.Ioc (origin + eta) stop →
      (∀ x z, 0 ≤ hamiltonPerturbedHarnackQuadraticValue
        (E := E) (I := I) (M := M) S origin phi psi t x z) →
      ∀ x z, hamiltonPerturbedHarnackQuadraticValue
          (E := E) (I := I) (M := M) S origin phi psi t x z = 0 →
        ∃ (extension : Real → ∀ y,
            HarnackCarrierFiber (E := E) (I := I) (M := M) y)
          (f : Real → M → Real) (timeDeriv : Real),
          extension t x = z ∧
          f t x = hamiltonPerturbedHarnackQuadraticValue
            (E := E) (I := I) (M := M) S origin phi psi
              t x (extension t x) ∧
          (∀ᶠ p in nhdsWithin (t, x)
              (Set.Ioc origin stop ×ˢ Set.univ),
            hamiltonPerturbedHarnackQuadraticValue
              (E := E) (I := I) (M := M) S origin phi psi
                p.1 p.2 (extension p.1 p.2) ≤ f p.1 p.2) ∧
          HasDerivWithinAt (fun s : Real => f s x) timeDeriv
            (Set.Ioc origin stop) t ∧
          MDifferentiableAt I 𝓘(Real, Real) (f t) x ∧
          (∀ᶠ y in nhds x,
            MDifferentiableAt I 𝓘(Real, Real) (f t) y) ∧
          MDiffAt (T% fun y : M =>
            gradientFun (I := I) (S.base.metric t) (f t) y) x ∧
          0 < timeDeriv - laplacian (I := I)
            (LeviCivita (I := I) (S.base.metric t))
              (S.base.metric t) (f t) x := by
    intro t ht hnonnegative x z hnull
    have htorigin : origin < t :=
      (lt_add_of_pos_right origin heta).trans ht.1
    have htOrigin : t ∈ Set.Ioc origin stop := ⟨htorigin, ht.2⟩
    have htClosed : t ∈ Set.Icc origin stop := ⟨htorigin.le, ht.2⟩
    have helapsed : t - origin ≤ stop - origin :=
      sub_le_sub_right ht.2 origin
    obtain ⟨U, hU, hxU, hbar, hbarSmooth, hbarEq, hbarUpper,
        _hbarGrad, hbarLap⟩ := hsupport t htClosed x
    apply exists_hamiltonPerturbedHarnackQuadraticValue_strict_support
      (I := I) (reactionK := reactionK) (S0 := stop - origin)
      (reactionB := reactionB) (reactionC := reactionC)
      (Ch := Ch) (barrierA := barrierA) (barrierB := barrierB)
      (kappa := kappa) (epsilon := epsilon)
      S hS htOrigin hregOrigin (sub_nonneg.mpr horiginStop.le) helapsed
      (fun k hk y => hderiv k hk t htClosed y)
      hReactionB hReactionCphi hReactionCpsiW hReactionCpsiU hCA hCB
      hkappa hepsilon.1 hsmall (hpsi1 t htOrigin)
      h hh x hU hxU hbar hbarSmooth hbarEq hbarUpper hbarLap
      (by simpa only [phi, psi] using hnonnegative) z
      (by simpa only [phi, psi] using hnull)
  have hpositive :=
    DifferentialGeometry.Analysis.Parabolic.strict_rank_one_support_of_compact_representatives
      (I := I)
      (fun t => LeviCivita (I := I) (S.base.metric t))
      (fun t => S.base.metric t)
      (fun t x z => hamiltonPerturbedHarnackQuadraticValue
        (E := E) (I := I) (M := M) S origin phi psi t x z)
      origin stop eta L heta hL hcontinuous hearlyValue hrepresent
      hmetricCompatible hstrictSupport
  intro t ht x U W hne
  have hvalue := hpositive t ht x (U, W)
  rw [hamiltonPerturbedHarnackQuadraticValue_of_ne_zero
    S origin phi psi t ht.1 x (U, W) hne] at hvalue
  simpa only [phi, psi] using hvalue

private theorem hamiltonHarnackQuadraticAt_nonneg_on_connected_slab
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alphaMinus origin stop C : Real}
    (hbuffer : alphaMinus < origin)
    (horiginStop : origin < stop)
    (hslab : Set.Icc alphaMinus stop ⊆ D.carrier)
    (hreg : Set.Ioc alphaMinus stop ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete
      (I := I) (S.base.metric alphaMinus))
    (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Set.Icc alphaMinus stop, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ Set.Icc origin stop, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ t, ∀ ht : t ∈ Set.Ioc origin stop, ∀ x : M,
      ∀ U : HamiltonHarnackTwoForm (TangentSpace I x),
      ∀ W : Tensor0SSpace 1 I x,
        0 ≤ hamiltonHarnackQuadraticAt (I := I) S
          ⟨origin, t, ht.1⟩ x U W := by
  obtain ⟨h, barrierA, barrierB, kappa, epsilon0, hepsilon0, hpositive⟩ :=
    exists_hamiltonPerturbedHarnackQuadraticAt_pos_on_connected_slab
      (I := I) S hS hbuffer horiginStop hslab hreg hcomplete hC hcurv hR
  intro t ht x U W
  by_cases hne : (U, W) = 0
  · have hU : U = 0 := congrArg Prod.fst hne
    have hW : W = 0 := congrArg Prod.snd hne
    rw [hU, hW]
    have hscale := hamiltonHarnackQuadraticAt_smul
      (I := I) S ⟨origin, t, ht.1⟩ x 0 U W
    have hzero : hamiltonHarnackQuadraticAt
        (I := I) S ⟨origin, t, ht.1⟩ x 0 0 = 0 := by
      simpa using hscale
    exact hzero.ge
  let q0 := hamiltonHarnackQuadraticAt
    (I := I) S ⟨origin, t, ht.1⟩ x U W
  let coefficient :=
    Real.exp (barrierA * (t - origin)) * h x / (t - origin) *
        normSq0S (I := I) (S.base.metric t) x 1 W +
      kappa * Real.exp (barrierB * (t - origin)) *
        normSq0S (I := I) (S.base.metric t) x 2 U.toTensor0S
  let epsilon : Nat → Real := fun n => epsilon0 * (1 / (n + 1 : Real))
  have hepsilon : Filter.Tendsto epsilon Filter.atTop (nhds 0) := by
    simpa only [epsilon, mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)))
  have hlimit : Filter.Tendsto
      (fun n => hamiltonPerturbedHarnackQuadraticAt (I := I) S
        ⟨origin, t, ht.1⟩
        (hamiltonBarrierPhi (epsilon n) barrierA origin h t x)
        (hamiltonBarrierPsi kappa (epsilon n) barrierB origin t) x U W)
      Filter.atTop (nhds q0) := by
    have hraw : Filter.Tendsto
        (fun n => q0 + epsilon n * coefficient) Filter.atTop (nhds q0) := by
      simpa using
        ((tendsto_const_nhds (x := q0)).add (hepsilon.mul_const coefficient))
    refine hraw.congr' (Filter.Eventually.of_forall fun n => ?_)
    simp only [hamiltonPerturbedHarnackQuadraticAt, hamiltonBarrierPhi,
      hamiltonBarrierPsi, HarnackClock.elapsed, q0, coefficient]
    ring
  have hnonnegative : ∀ n : Nat, 0 ≤
      hamiltonPerturbedHarnackQuadraticAt (I := I) S
        ⟨origin, t, ht.1⟩
        (hamiltonBarrierPhi (epsilon n) barrierA origin h t x)
        (hamiltonBarrierPsi kappa (epsilon n) barrierB origin t) x U W := by
    intro n
    have hepsilonPos : 0 < epsilon n := by
      dsimp only [epsilon]
      positivity
    have hepsilonLe : epsilon n ≤ epsilon0 := by
      dsimp only [epsilon]
      have hfrac : (1 / (n + 1 : Real)) ≤ 1 := by
        apply (div_le_one (by positivity : 0 < (n + 1 : Real))).2
        norm_num
      exact mul_le_of_le_one_right hepsilon0.le hfrac
    exact (hpositive (epsilon n) ⟨hepsilonPos, hepsilonLe⟩
      t ht x U W hne).le
  exact ge_of_tendsto hlimit (Filter.Eventually.of_forall hnonnegative)

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] in
private noncomputable def restrictOpenTangentEquiv
    (O : TopologicalSpace.Opens M) (x : O) :
    TangentSpace I x ≃L[Real] TangentSpace I (x : M) :=
  (tangentSpaceModelContinuousLinearEquiv (I := I) x).trans
    (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] in
private theorem restrictOpenTangentEquiv_apply
    (O : TopologicalSpace.Opens M) (x : O) (V : TangentSpace I x) :
    restrictOpenTangentEquiv (I := I) O x V = V := by
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).injective
  change tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)
      ((tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) x V)) =
    tangentSpaceModelContinuousLinearEquiv (I := I) (x : M) V
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (tangentSpaceModelContinuousLinearEquiv_apply (I := I) x V).trans
    (tangentSpaceModelContinuousLinearEquiv_apply (I := I) (x : M) V).symm

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] in
private theorem restrictOpenTangentEquiv_symm_apply
    (O : TopologicalSpace.Opens M) (x : O) (V : TangentSpace I (x : M)) :
    (restrictOpenTangentEquiv (I := I) O x).symm V = V := by
  exact (restrictOpenTangentEquiv_apply (I := I) O x
    ((restrictOpenTangentEquiv (I := I) O x).symm V)).symm.trans
      ((restrictOpenTangentEquiv (I := I) O x).apply_symm_apply V)

omit [SigmaCompactSpace M] in
private theorem hamiltonPAt_restrictOpen
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (O : TopologicalSpace.Opens M)
    [T2Space O] [BoundarylessManifold I O]
    [IsManifold I 1 O] [IsManifold I 2 O]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) O]
    (x : O) (A B C : TangentSpace I (x : M)) :
    hamiltonPAt (I := I) (g.restrictOpen (I := I) O) x
        ![(restrictOpenTangentEquiv (I := I) O x).symm A,
          (restrictOpenTangentEquiv (I := I) O x).symm B,
          (restrictOpenTangentEquiv (I := I) O x).symm C] =
      hamiltonPAt (I := I) g (x : M) ![A, B, C] := by
  let eM := restrictOpenTangentEquiv (I := I) O x
  change hamiltonPAt (I := I) (g.restrictOpen (I := I) O) x
      ![eM.symm A, eM.symm B, eM.symm C] =
    hamiltonPAt (I := I) g (x : M) ![A, B, C]
  have hABC := DifferentialGeometry.CheegerGromovCompactness.ricCovTower_restrictOpen
    (I := I) g O 1 x ![eM.symm A, eM.symm B, eM.symm C]
  have hBAC := DifferentialGeometry.CheegerGromovCompactness.ricCovTower_restrictOpen
    (I := I) g O 1 x ![eM.symm B, eM.symm A, eM.symm C]
  have hABC' : DifferentialGeometry.CheegerGromovCompactness.ricCovTower
        (I := I) (g.restrictOpen (I := I) O)
        (g.restrictOpen (I := I) O) 1 x
          ![eM.symm A, eM.symm B, eM.symm C] =
      DifferentialGeometry.CheegerGromovCompactness.ricCovTower
        (I := I) g g 1 (x : M) ![A, B, C] := by
    calc
      _ = DifferentialGeometry.CheegerGromovCompactness.ricCovTower
          (I := I) g g 1 (x : M)
            ![eM.symm A, eM.symm B, eM.symm C] := hABC
      _ = _ := by congr 1
  have hBAC' : DifferentialGeometry.CheegerGromovCompactness.ricCovTower
        (I := I) (g.restrictOpen (I := I) O)
        (g.restrictOpen (I := I) O) 1 x
          ![eM.symm B, eM.symm A, eM.symm C] =
      DifferentialGeometry.CheegerGromovCompactness.ricCovTower
        (I := I) g g 1 (x : M) ![B, A, C] := by
    calc
      _ = DifferentialGeometry.CheegerGromovCompactness.ricCovTower
          (I := I) g g 1 (x : M)
            ![eM.symm B, eM.symm A, eM.symm C] := hBAC
      _ = _ := by congr 1
  have hswapO :
      (fun i => ![eM.symm A, eM.symm B, eM.symm C]
        ((Equiv.swap (0 : Fin 3) 1) i)) =
        ![eM.symm B, eM.symm A, eM.symm C] := by
    funext i
    fin_cases i <;> rfl
  have hswapM :
      (fun i => ![A, B, C] ((Equiv.swap (0 : Fin 3) 1) i)) =
        ![B, A, C] := by
    funext i
    fin_cases i <;> rfl
  unfold hamiltonPAt hamiltonP
  simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.domDomCongr_apply]
  rw [hswapO, hswapM]
  simpa [DifferentialGeometry.CheegerGromovCompactness.ricCovTower,
    DifferentialGeometry.CheegerGromovCompactness.iterCov, metricNablaRic,
    metricRicci, metricCov, DifferentialGeometry.CheegerGromovCompactness.covStep] using
    congrArg₂ (fun p q : Real => p - q) hABC' hBAC'

omit [SigmaCompactSpace M] in
private theorem metricNabla2Ric_restrictOpen
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (O : TopologicalSpace.Opens M)
    [T2Space O] [BoundarylessManifold I O]
    [IsManifold I 1 O] [IsManifold I 2 O]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) O]
    (x : O) (A B C D : TangentSpace I (x : M)) :
    metricNabla2Ric (I := I) (M := O) (g.restrictOpen (I := I) O) x
        ![(restrictOpenTangentEquiv (I := I) O x).symm A,
          (restrictOpenTangentEquiv (I := I) O x).symm B,
          (restrictOpenTangentEquiv (I := I) O x).symm C,
          (restrictOpenTangentEquiv (I := I) O x).symm D] =
      metricNabla2Ric (I := I) (M := M) g (x : M) ![A, B, C, D] := by
  let eM := restrictOpenTangentEquiv (I := I) O x
  have h := DifferentialGeometry.CheegerGromovCompactness.ricCovTower_restrictOpen
    (I := I) g O 2 x ![eM.symm A, eM.symm B, eM.symm C, eM.symm D]
  have hleft : metricNabla2Ric (I := I) (M := O)
      (g.restrictOpen (I := I) O) x
        ![eM.symm A, eM.symm B, eM.symm C, eM.symm D] =
      DifferentialGeometry.CheegerGromovCompactness.ricCovTower
        (I := I) (g.restrictOpen (I := I) O)
          (g.restrictOpen (I := I) O) 2 x
            ![eM.symm A, eM.symm B, eM.symm C, eM.symm D] := by rfl
  have hright : metricNabla2Ric (I := I) (M := M) g (x : M)
        ![A, B, C, D] =
      DifferentialGeometry.CheegerGromovCompactness.ricCovTower
        (I := I) g g 2 (x : M) ![A, B, C, D] := by rfl
  rw [hleft, hright]
  calc
    _ = DifferentialGeometry.CheegerGromovCompactness.ricCovTower
        (I := I) g g 2 (x : M)
          ![eM.symm A, eM.symm B, eM.symm C, eM.symm D] := h
    _ = _ := by congr 1

omit [SigmaCompactSpace M] in
private theorem metricRm04_restrictOpen
    (g : SmoothRiemannianMetric I M) (O : TopologicalSpace.Opens M)
    [T2Space O] [IsManifold I 1 O]
    (x : O) (A B C D : TangentSpace I (x : M)) :
    metricRm04 (I := I) (M := O) (g.restrictOpen (I := I) O) x
        ![(restrictOpenTangentEquiv (I := I) O x).symm A,
          (restrictOpenTangentEquiv (I := I) O x).symm B,
          (restrictOpenTangentEquiv (I := I) O x).symm C,
          (restrictOpenTangentEquiv (I := I) O x).symm D] =
      metricRm04 (I := I) (M := M) g (x : M) ![A, B, C, D] := by
  let eM := restrictOpenTangentEquiv (I := I) O x
  have hrestrict : metricRm04 (I := I) (M := O)
        (g.restrictOpen (I := I) O) x
          ![eM.symm A, eM.symm B, eM.symm C, eM.symm D] =
      metricRm04 (I := I) (M := M) g (x : M)
        ![eM.symm A, eM.symm B, eM.symm C, eM.symm D] := by
    have hraw := DifferentialGeometry.CheegerGromovCompactness.metricRm04_restrictOpen_eval
      (I := I) g O x ![eM.symm A, eM.symm B, eM.symm C, eM.symm D]
    simp only [mfderiv_subtype_val_apply (I := I) O x] at hraw
    exact hraw.trans (congrArg (metricRm04 (I := I) (M := M) g (x : M))
      (by funext i; rfl))
  calc
    _ = metricRm04 (I := I) (M := M) g (x : M)
        ![eM.symm A, eM.symm B, eM.symm C, eM.symm D] := hrestrict
    _ = _ := by
      apply congrArg (metricRm04 (I := I) (M := M) g (x : M))
      funext i
      fin_cases i <;>
        apply restrictOpenTangentEquiv_symm_apply

omit [SigmaCompactSpace M] in
private theorem metricRicci_restrictOpen
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (O : TopologicalSpace.Opens M)
    [T2Space O] [BoundarylessManifold I O]
    [IsManifold I 1 O]
    (x : O) (A B : TangentSpace I (x : M)) :
    metricRicci (I := I) (M := O) (g.restrictOpen (I := I) O) x
        ![(restrictOpenTangentEquiv (I := I) O x).symm A,
          (restrictOpenTangentEquiv (I := I) O x).symm B] =
      metricRicci (I := I) (M := M) g (x : M) ![A, B] := by
  let eM := restrictOpenTangentEquiv (I := I) O x
  have hrestrict : metricRicci (I := I) (M := O)
        (g.restrictOpen (I := I) O) x ![eM.symm A, eM.symm B] =
      metricRicci (I := I) (M := M) g (x : M)
        ![eM.symm A, eM.symm B] := by
    have hraw := DifferentialGeometry.CheegerGromovCompactness.metricRicci_restrictOpen_eval
      (I := I) g O x ![eM.symm A, eM.symm B]
    simp only [mfderiv_subtype_val_apply (I := I) O x] at hraw
    exact hraw.trans (congrArg (metricRicci (I := I) (M := M) g (x : M))
      (by funext i; rfl))
  calc
    _ = metricRicci (I := I) (M := M) g (x : M)
        ![eM.symm A, eM.symm B] := hrestrict
    _ = _ := by
      apply congrArg (metricRicci (I := I) (M := M) g (x : M))
      funext i
      fin_cases i <;>
        apply restrictOpenTangentEquiv_symm_apply

omit [SigmaCompactSpace M] in
private theorem hamiltonHarnackQuadraticAt_restrictOpen
    [BoundarylessManifold I M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (O : TopologicalSpace.Opens M)
    [SigmaCompactSpace O] [T2Space O] [BoundarylessManifold I O]
    [IsManifold I 1 O] [IsManifold I 2 O]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) O]
    (clock : HarnackClock) (ht : clock.time ∈ D.regular) (x : O)
    (U : HamiltonHarnackTwoForm (TangentSpace I (x : M)))
    (W : Tensor0SSpace 1 I (x : M)) :
    let eM := restrictOpenTangentEquiv (I := I) O x
    let UO : HamiltonHarnackTwoForm (TangentSpace I x) :=
      U.compContinuousLinearMap eM.toContinuousLinearMap
    let WO : Tensor0SSpace 1 I x :=
      W.compContinuousLinearMap (fun _ => eM.toContinuousLinearMap)
    hamiltonHarnackQuadraticAt (I := I)
        (DifferentialGeometry.CheegerGromovCompactness.solutionOnRestrictOpen
          (I := I) S O) clock x UO WO =
      hamiltonHarnackQuadraticAt (I := I) S clock (x : M) U W := by
  dsimp only
  let eM := restrictOpenTangentEquiv (I := I) O x
  let UO : HamiltonHarnackTwoForm (TangentSpace I x) :=
    U.compContinuousLinearMap eM.toContinuousLinearMap
  let WO : Tensor0SSpace 1 I x :=
    W.compContinuousLinearMap (fun _ => eM.toContinuousLinearMap)
  let SO := DifferentialGeometry.CheegerGromovCompactness.solutionOnRestrictOpen
    (I := I) S O
  have hSO : IsSolutionOn (I := I) SO :=
    DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_restrictOpen
      (I := I) S hS O
  obtain ⟨basisM, horthM⟩ := exists_orthonormal_basis
    (I := I) (M := M) (S.base.metric clock.time) (x : M)
  let basisO := basisM.map eM.symm.toLinearEquiv
  have hbasisO (a) : basisO a = eM.symm (basisM a) := by
    rfl
  have horthO : ∀ i j,
      (SO.base.metric clock.time).inner x (basisO i) (basisO j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    change (S.base.metric clock.time).inner (x : M)
      (eM.symm (basisM i)) (eM.symm (basisM j)) = _
    rw [restrictOpenTangentEquiv_symm_apply,
      restrictOpenTangentEquiv_symm_apply]
    exact horthM i j
  have hinvM : MetricInverseInBasis (I := I) (M := M)
      (S.base.metric clock.time) (x : M) basisM
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I (x : M))))) :=
    metricInverseInBasis_of_orthonormal (I := I) (M := M)
      (S.base.metric clock.time) basisM horthM
  have hinvO : MetricInverseInBasis (I := I) (M := O)
      (SO.base.metric clock.time) x basisO
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I (x : M))))) :=
    metricInverseInBasis_of_orthonormal (I := I) (M := O)
      (SO.base.metric clock.time) basisO horthO
  have hquadraticO := hamiltonHarnackQuadraticAt_eq_hamiltonBlockQuadratic
    (I := I) SO clock x UO WO basisO hinvO
  have hquadraticM := hamiltonHarnackQuadraticAt_eq_hamiltonBlockQuadratic
    (I := I) S clock (x : M) U W basisM hinvM
  have hK (a b c d : Fin (Module.finrank Real (TangentSpace I (x : M)))) :
      tensor04StandardAt (I := I) (M := O) (SO.base.rm04 clock.time x)
          (basisO a) (basisO b) (basisO d) (basisO c) =
        tensor04StandardAt (I := I) (M := M) (S.base.rm04 clock.time (x : M))
          (basisM a) (basisM b) (basisM d) (basisM c) := by
    change metricRm04 (I := I) (M := O)
        ((S.base.metric clock.time).restrictOpen (I := I) O) x
          (vec4 (basisO a) (basisO b) (basisO d) (basisO c)) =
      metricRm04 (I := I) (M := M) (S.base.metric clock.time) (x : M)
        (vec4 (basisM a) (basisM b) (basisM d) (basisM c))
    have hvecO : vec4 (basisO a) (basisO b) (basisO d) (basisO c) =
        ![basisO a, basisO b, basisO d, basisO c] := by
      funext i
      fin_cases i <;> rfl
    have hvecM : vec4 (basisM a) (basisM b) (basisM d) (basisM c) =
        ![basisM a, basisM b, basisM d, basisM c] := by
      funext i
      fin_cases i <;> rfl
    rw [hvecO, hvecM]
    simpa only [hbasisO] using metricRm04_restrictOpen
      (I := I) (S.base.metric clock.time) O x
        (basisM a) (basisM b) (basisM d) (basisM c)
  have hP (a b c : Fin (Module.finrank Real (TangentSpace I (x : M)))) :
      hamiltonPAt (I := I) (SO.base.metric clock.time) x
          ![basisO a, basisO b, basisO c] =
        hamiltonPAt (I := I) (S.base.metric clock.time) (x : M)
          ![basisM a, basisM b, basisM c] := by
    change hamiltonPAt (I := I)
        ((S.base.metric clock.time).restrictOpen (I := I) O) x
          ![basisO a, basisO b, basisO c] =
      hamiltonPAt (I := I) (S.base.metric clock.time) (x : M)
        ![basisM a, basisM b, basisM c]
    simpa only [hbasisO] using hamiltonPAt_restrictOpen
      (I := I) (S.base.metric clock.time) O x
        (basisM a) (basisM b) (basisM c)
  have hM (a b : Fin (Module.finrank Real (TangentSpace I (x : M)))) :
      hamiltonMAt (I := I) clock (SO.base.metric clock.time) x
          ![basisO a, basisO b] =
        hamiltonMAt (I := I) clock (S.base.metric clock.time) (x : M)
          ![basisM a, basisM b] := by
    have hvecO : vec2 (basisO a) (basisO b) = ![basisO a, basisO b] := by
      funext i
      fin_cases i <;> rfl
    have hvecM : vec2 (basisM a) (basisM b) = ![basisM a, basisM b] := by
      funext i
      fin_cases i <;> rfl
    change hamiltonMAt (I := I) clock (SO.family.metric clock.time) x
        ![basisO a, basisO b] =
      hamiltonMAt (I := I) clock (S.family.metric clock.time) (x : M)
        ![basisM a, basisM b]
    rw [← hvecO, ← hvecM,
      hamiltonMAt_apply_basis (I := I) SO hSO clock ht x basisO
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I (x : M))))) hinvO a b,
      hamiltonMAt_apply_basis (I := I) S hS clock ht (x : M) basisM
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I (x : M))))) hinvM a b]
    simp only [hbasisO]
    simp only [SolutionOn.family_metric]
    dsimp only [SO, DifferentialGeometry.CheegerGromovCompactness.solutionOnRestrictOpen]
    have hvec2 (A B : TangentSpace I x) : vec2 A B = ![A, B] := by
      funext i
      fin_cases i <;> rfl
    have hvec4 (A B C D : TangentSpace I x) :
        vec4 A B C D = ![A, B, C, D] := by
      funext i
      fin_cases i <;> rfl
    have hvec2M (A B : TangentSpace I (x : M)) : vec2 A B = ![A, B] := by
      funext i
      fin_cases i <;> rfl
    have hvec4M (A B C D : TangentSpace I (x : M)) :
        vec4 A B C D = ![A, B, C, D] := by
      funext i
      fin_cases i <;> rfl
    simp_rw [hvec2, hvec4, hvec2M, hvec4M]
    have hnabla2 (A B C D : TangentSpace I (x : M)) :
        metricNabla2Ric (I := I) (M := O)
            ((S.base.metric clock.time).restrictOpen (I := I) O) x
              ![eM.symm A, eM.symm B, eM.symm C, eM.symm D] =
          metricNabla2Ric (I := I) (M := M) (S.base.metric clock.time)
            (x : M) ![A, B, C, D] := by
      simpa only [eM] using metricNabla2Ric_restrictOpen
        (I := I) (S.base.metric clock.time) O x A B C D
    have hRm (A B C D : TangentSpace I (x : M)) :
        metricRm04 (I := I) (M := O)
            ((S.base.metric clock.time).restrictOpen (I := I) O) x
              ![eM.symm A, eM.symm B, eM.symm C, eM.symm D] =
          metricRm04 (I := I) (M := M) (S.base.metric clock.time)
            (x : M) ![A, B, C, D] := by
      simpa only [eM] using metricRm04_restrictOpen
        (I := I) (S.base.metric clock.time) O x A B C D
    have hRic (A B : TangentSpace I (x : M)) :
        metricRicci (I := I) (M := O)
            ((S.base.metric clock.time).restrictOpen (I := I) O) x
              ![eM.symm A, eM.symm B] =
          metricRicci (I := I) (M := M) (S.base.metric clock.time)
            (x : M) ![A, B] := by
      simpa only [eM] using metricRicci_restrictOpen
        (I := I) (S.base.metric clock.time) O x A B
    simp_rw [hnabla2, hRm, hRic]
  have hU (a b : Fin (Module.finrank Real (TangentSpace I (x : M)))) :
      UO ![basisO a, basisO b] = U ![basisM a, basisM b] := by
    change U (eM.toContinuousLinearMap ∘ ![basisO a, basisO b]) =
      U ![basisM a, basisM b]
    apply congrArg U
    funext i
    fin_cases i
    · change eM (basisO a) = basisM a
      rw [hbasisO]
      exact eM.apply_symm_apply (basisM a)
    · change eM (basisO b) = basisM b
      rw [hbasisO]
      exact eM.apply_symm_apply (basisM b)
  have hW (a : Fin (Module.finrank Real (TangentSpace I (x : M)))) :
      WO ![basisO a] = W ![basisM a] := by
    change W (fun i => eM.toContinuousLinearMap (![basisO a] i)) =
      W ![basisM a]
    apply congrArg W
    funext i
    fin_cases i
    change eM (basisO a) = basisM a
    rw [hbasisO]
    exact eM.apply_symm_apply (basisM a)
  rw [hquadraticO, hquadraticM]
  unfold hamiltonBlockQuadratic hamiltonBlockPolarized
  simp_rw [hK, hP, hM, hU, hW]

private theorem hamiltonHarnackQuadraticAt_nonneg_on_slab
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {alphaMinus origin stop C : Real}
    (hbuffer : alphaMinus < origin)
    (horiginStop : origin < stop)
    (hslab : Set.Icc alphaMinus stop ⊆ D.carrier)
    (hreg : Set.Ioc alphaMinus stop ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete
      (I := I) (S.base.metric alphaMinus))
    (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Set.Icc alphaMinus stop, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ Set.Icc origin stop, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ t, ∀ ht : t ∈ Set.Ioc origin stop, ∀ x : M,
      ∀ U : HamiltonHarnackTwoForm (TangentSpace I x),
      ∀ W : Tensor0SSpace 1 I x,
        0 ≤ hamiltonHarnackQuadraticAt (I := I) S
          ⟨origin, t, ht.1⟩ x U W := by
  intro t ht x U W
  let : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  let O : TopologicalSpace.Opens M :=
    ⟨connectedComponent x, isOpen_connectedComponent⟩
  let : SigmaCompactSpace O := isClosed_connectedComponent.sigmaCompactSpace
  let xO : O := ⟨x, mem_connectedComponent⟩
  let : ConnectedSpace O :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : IsManifold I 1 O := IsManifold.of_le
    (I := I) (M := O) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I 2 O := IsManifold.of_le
    (I := I) (M := O) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) O := by
    change IsManifold I ∞ O
    infer_instance
  let SO := DifferentialGeometry.CheegerGromovCompactness.solutionOnRestrictOpen
    (I := I) S O
  have hSO : IsSolutionOn (I := I) SO :=
    DifferentialGeometry.CheegerGromovCompactness.isSolutionOn_restrictOpen
      (I := I) S hS O
  have hcompleteO : RiemannianMetricComplete
      (I := I) (SO.base.metric alphaMinus) := by
    change RiemannianMetricComplete (I := I)
      ((S.base.metric alphaMinus).restrictOpen (I := I) O)
    exact hcomplete.restrictOpen O isClosed_connectedComponent
  have hcurvO : ∀ s ∈ Set.Icc alphaMinus stop, ∀ y : O,
      normSq0S (I := I) (SO.base.metric s) y 4 (SO.base.rm04 s y) ≤ C := by
    intro s hs y
    change normSq0S (I := I) ((S.base.metric s).restrictOpen (I := I) O)
      y 4 (metricRm04 (I := I) (M := O)
        ((S.base.metric s).restrictOpen (I := I) O) y) ≤ C
    rw [DifferentialGeometry.CheegerGromovCompactness.normSq0S_restrictOpen_apply]
    have htensor : metricRm04 (I := I) (M := O)
          ((S.base.metric s).restrictOpen (I := I) O) y =
        metricRm04 (I := I) (M := M) (S.base.metric s) (y : M) := by
      ext slots
      have h := DifferentialGeometry.CheegerGromovCompactness.metricRm04_restrictOpen_eval
        (I := I) (S.base.metric s) O y slots
      simp only [mfderiv_subtype_val_apply (I := I) O y] at h
      exact h.trans (congrArg
        (metricRm04 (I := I) (M := M) (S.base.metric s) (y : M))
          (by funext i; rfl))
    rw [htensor]
    exact hcurv s hs (y : M)
  have hRO : ∀ s ∈ Set.Icc origin stop, ∀ y : O,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := O) (SO.base.metric s) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := O) := by
    intro s hs y
    rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
    intro n c v w
    have h :=
      (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) (M := M) (S.base.metric s) (y : M)).mp
        (hR s hs (y : M)) n c (fun i => v i) (fun i => w i)
    simpa only [SO, DifferentialGeometry.CheegerGromovCompactness.solutionOnRestrictOpen,
      metricRm04StandardAt_restrictOpen,
      mfderiv_subtype_val_apply (I := I) O y] using h
  let clock : HarnackClock := ⟨origin, t, ht.1⟩
  have htreg : t ∈ D.regular :=
    hreg ⟨hbuffer.trans ht.1, ht.2⟩
  let eM := restrictOpenTangentEquiv (I := I) O xO
  let UO : HamiltonHarnackTwoForm (TangentSpace I xO) :=
    U.compContinuousLinearMap eM.toContinuousLinearMap
  let WO : Tensor0SSpace 1 I xO :=
    W.compContinuousLinearMap (fun _ => eM.toContinuousLinearMap)
  have hnonnegative := hamiltonHarnackQuadraticAt_nonneg_on_connected_slab
    (I := I) SO hSO hbuffer horiginStop hslab hreg hcompleteO hC hcurvO hRO
      t ht xO UO WO
  have hrestrict := hamiltonHarnackQuadraticAt_restrictOpen
    (I := I) S hS O clock htreg xO U W
  change hamiltonHarnackQuadraticAt (I := I) SO clock xO UO WO =
    hamiltonHarnackQuadraticAt (I := I) S clock x U W at hrestrict
  rw [hrestrict] at hnonnegative
  exact hnonnegative

theorem hamilton_matrix_harnack
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (clock : HarnackClock)
    (hclock : Set.Icc clock.origin clock.time ⊆ D.regular)
    (x : M) (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) :
    0 ≤ hamiltonHarnackQuadraticAt (I := I) S clock x U W := by
  have horigin : clock.origin ∈ D.regular :=
    hclock ⟨le_rfl, clock.origin_lt_time.le⟩
  have htime : clock.time ∈ D.regular :=
    hclock ⟨clock.origin_lt_time.le, le_rfl⟩
  obtain ⟨alphaMinus, originUpper, horiginIoo, horiginRegular⟩ :=
    D.exists_Icc_regular horigin
  obtain ⟨timeLower, stop, htimeIoo, htimeRegular⟩ :=
    D.exists_Icc_regular htime
  have hregular : Set.Icc alphaMinus stop ⊆ D.regular := by
    intro s hs
    by_cases hsOrigin : s ≤ clock.origin
    · exact horiginRegular ⟨hs.1, hsOrigin.trans horiginIoo.2.le⟩
    by_cases hsTime : s ≤ clock.time
    · exact hclock ⟨le_of_not_ge hsOrigin, hsTime⟩
    · exact htimeRegular ⟨htimeIoo.1.le.trans (le_of_not_ge hsTime), hs.2⟩
  obtain ⟨C, hCbound⟩ := hcurv alphaMinus stop hregular
  have hC : 0 ≤ C :=
    (normSq0S_nonneg (I := I) (S.base.metric alphaMinus) x 4
      (S.base.rm04 alphaMinus x)).trans
        (hCbound alphaMinus ⟨le_rfl, horiginIoo.1.le.trans
          (clock.origin_lt_time.trans htimeIoo.2).le⟩ x)
  apply hamiltonHarnackQuadraticAt_nonneg_on_slab
      (I := I) S hS horiginIoo.1
      (clock.origin_lt_time.trans htimeIoo.2)
      (fun s hs ↦ D.regular_subset (hregular hs))
      (fun s hs ↦ hregular ⟨hs.1.le, hs.2⟩)
      (hcomplete alphaMinus (hregular ⟨le_rfl,
        horiginIoo.1.le.trans (clock.origin_lt_time.trans htimeIoo.2).le⟩))
      hC hCbound
      (fun s hs ↦ hR s (hregular
        ⟨horiginIoo.1.le.trans hs.1, hs.2⟩))
      clock.time ⟨clock.origin_lt_time, htimeIoo.2.le⟩ x U W

theorem hamilton_ancient_matrix_harnack
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t : Real} (hregular : Set.Iic t ⊆ D.regular)
    (x : M) (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) :
    0 ≤ hamiltonUnshiftedHarnackQuadraticAt (I := I) S t x U W := by
  let q := hamiltonUnshiftedHarnackQuadraticAt (I := I) S t x U W
  let c := inner0S (I := I) (S.base.metric t) x 2
    (metricRicci (I := I) (M := M) (S.base.metric t) x) (W.product W)
  apply hamilton_ancient_matrix_limit_of_all_origins
    (q := q) (c := c) (t := t)
  intro alpha halpha
  let clock : HarnackClock := ⟨alpha, t, halpha⟩
  have hclock : Set.Icc alpha t ⊆ D.regular := by
    intro s hs
    exact hregular hs.2
  have hshift := hamilton_matrix_harnack (I := I) S hS hcomplete hcurv hR
    clock hclock x U W
  rw [hamiltonHarnackQuadraticAt_eq_unshifted_add
    (I := I) S clock x U W] at hshift
  simpa only [q, c, clock, HarnackClock.elapsed] using hshift

theorem hamilton_matrix_harnack_finite_origin
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ a b : Real, Set.Icc a b ⊆ D.regular →
      ∃ C : Real, ∀ t ∈ Set.Icc a b, ∀ x : M,
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t : Real} (ht : 0 < t) (hregular : Set.Ioc 0 t ⊆ D.regular)
    (x : M) (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) :
    0 ≤ hamiltonHarnackQuadraticAt (I := I) S ⟨0, t, ht⟩ x U W := by
  let q := hamiltonUnshiftedHarnackQuadraticAt (I := I) S t x U W
  let c := inner0S (I := I) (S.base.metric t) x 2
    (metricRicci (I := I) (M := M) (S.base.metric t) x) (W.product W)
  have hlimit : 0 ≤ q + c / (2 * t) :=
    hamilton_finite_origin_matrix_limit ht (fun alpha halpha => by
      let clock : HarnackClock := ⟨alpha, t, halpha.2⟩
      have hclock : Set.Icc alpha t ⊆ D.regular := by
        intro s hs
        exact hregular ⟨halpha.1.trans_le hs.1, hs.2⟩
      have hshift := hamilton_matrix_harnack (I := I) S hS hcomplete hcurv hR
        clock hclock x U W
      rw [hamiltonHarnackQuadraticAt_eq_unshifted_add
        (I := I) S clock x U W] at hshift
      simpa only [q, c, clock, HarnackClock.elapsed] using hshift)
  rw [hamiltonHarnackQuadraticAt_eq_unshifted_add
    (I := I) S ⟨0, t, ht⟩ x U W]
  simpa only [q, c, HarnackClock.elapsed, sub_zero] using hlimit

omit [SigmaCompactSpace M] in
theorem hamilton_matrix_harnack_of_compact
    [I.Boundaryless] [NeZero (Module.finrank Real E)] [CompactSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hR : ∀ t ∈ D.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t : Real} (ht : 0 < t) (hregular : Set.Ioc 0 t ⊆ D.regular)
    (x : M) (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) :
    0 ≤ hamiltonHarnackQuadraticAt (I := I) S ⟨0, t, ht⟩ x U W := by
  apply hamilton_matrix_harnack_finite_origin (I := I) S hS
    (fun s _ ↦ RiemannianMetricComplete.of_compact (I := I) (S.base.metric s))
    ?_ hR ht hregular x U W
  intro a b hab
  let P := {s : Real // s ∈ Set.Icc a b} × M
  let : CompactSpace {s : Real // s ∈ Set.Icc a b} :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace P := inferInstance
  have hRm : Continuous
      (fun q : P => Bundle.TotalSpace.mk' (Tensor0SModel 4 Real E) q.2
        (S.base.rm04 q.1.1 q.2)) :=
    hS.rm04Cont.mono (fun s hs ↦ D.regular_subset (hab hs))
  have hnorm : Continuous
      (fun q : P => normSq0S (I := I) (S.base.metric q.1.1)
        q.2 4 (S.base.rm04 q.1.1 q.2)) := by
    simpa only [SolutionOn.family_metric] using
      metricFamilyNormSq_sections_continuous
        (I := I) (G := S.family) hS.smoothMetric hab
        (fun q : P => q.1) continuous_fst
        (fun q : P => q.2) continuous_snd
        (fun q : P => S.base.rm04 q.1.1 q.2) hRm
  obtain ⟨C, hC⟩ := (isCompact_range hnorm).bddAbove
  exact ⟨C, fun s hs y ↦ hC ⟨(⟨s, hs⟩, y), rfl⟩⟩

omit [SigmaCompactSpace M] in
theorem hamilton_matrix_harnack_of_compact_of_initial_nonnegative
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hdim : ∀ y : M, Module.finrank Real (TangentSpace I y) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : ∀ y : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S.base.metric 0) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t : Real} (ht : t ∈ Set.Ioo 0 T)
    (x : M) (U : HamiltonHarnackTwoForm (TangentSpace I x))
    (W : Tensor0SSpace 1 I x) :
    0 ≤ hamiltonHarnackQuadraticAt (I := I) S ⟨0, t, ht.1⟩ x U W := by
  let : NeZero (Module.finrank Real E) := ⟨by
    have hx : Module.finrank Real E = 3 := hdim x
    omega⟩
  have hpreserved := metric_curvature_operator_nonnegative_preserved
    (I := I) hS hdim (le_of_lt (ht.1.trans ht.2)) hTsub hTreg hinit
  let D' := RealTimeInterval.openInterval 0 T t ht
  let S' := S.timeRestrict D'
  have hS' : IsSolutionOn (I := I) S' := by
    apply isSolutionOn_timeRestrict (I := I) hS.isSolution
    · intro s hs
      change s ∈ Set.Ioo 0 T at hs
      exact hTsub ⟨hs.1.le, hs.2.le⟩
    · intro s hs
      change s ∈ Set.Ioo 0 T at hs
      exact hTreg ⟨hs.1, hs.2.le⟩
  have hR' : ∀ s ∈ D'.regular, ∀ y : M,
      metricAlgebraicCurvatureTensorAt
        (I := I) (M := M) (S'.base.metric s) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro s hs y
    change s ∈ Set.Ioo 0 T at hs
    change metricAlgebraicCurvatureTensorAt
      (I := I) (M := M) (S.base.metric s) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)
    exact hpreserved s ⟨hs.1.le, hs.2.le⟩ y
  have hregular' : Set.Ioc 0 t ⊆ D'.regular := by
    intro s hs
    change s ∈ Set.Ioo 0 T
    exact ⟨hs.1, hs.2.trans_lt ht.2⟩
  exact hamilton_matrix_harnack_of_compact
    (I := I) S' hS' hR' ht.1 hregular' x U W

omit [SigmaCompactSpace M] in
theorem exists_hamiltonHarnackQuadratic_minimizer
    [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (origin : Real) {T : Set Real}
    (hT : IsCompact T) (hTD : T ⊆ D.regular)
    (horigin : ∀ t ∈ T, origin < t)
    (gRef : SmoothRiemannianMetric I M)
    {K : Set M} (hK : IsCompact K)
    (hne : Set.Nonempty
      {q : {t : Real // t ∈ T} ×
          HarnackCarrierTotal (E := E) (I := I) (M := M) |
        q.2.proj ∈ K ∧
          harnackCarrierNormSq (E := E) (I := I) (M := M) gRef q.2 = 1}) :
    ∃ q ∈
        {q : {t : Real // t ∈ T} ×
            HarnackCarrierTotal (E := E) (I := I) (M := M) |
          q.2.proj ∈ K ∧
            harnackCarrierNormSq (E := E) (I := I) (M := M) gRef q.2 = 1},
      IsMinOn
        (fun p : {t : Real // t ∈ T} ×
            HarnackCarrierTotal (E := E) (I := I) (M := M) =>
          hamiltonHarnackQuadraticAt (I := I) S
            ⟨origin, p.1.1, horigin p.1.1 p.1.2⟩
            p.2.proj p.2.2.1 p.2.2.2)
        {p : {t : Real // t ∈ T} ×
            HarnackCarrierTotal (E := E) (I := I) (M := M) |
          p.2.proj ∈ K ∧
            harnackCarrierNormSq (E := E) (I := I) (M := M) gRef p.2 = 1}
        q := by
  have hcompact := harnackCarrierNormSq_time_level_isCompact
    (E := E) (I := I) (M := M) gRef hT hK
  exact hcompact.exists_isMinOn hne
    (hamiltonHarnackQuadratic_continuous
      (I := I) S hS origin hTD horigin).continuousOn

end DifferentialGeometry.PDE.RicciFlow
