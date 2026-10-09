import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.CommonScaleOrientedHornNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatumOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteMetricEventDebit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower
import DifferentialGeometry.Geometry.Neck.ScalarCutReindex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
open Set Function TopologicalSpace Manifold MeasureTheory Filter
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Manifold DifferentialGeometry.PDE.RicciFlow.StandardCap
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u v
private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
attribute [local instance] threeBallChartedSpace threeBall_isManifold
private local instance {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      D.slab.terminalRegularOpen.isOpen)

private theorem retained_terminal_reindex
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]
    {ι : Type v} {κ : Type} {δ : ι → ℝ}
    (U : Opens M) (g : SmoothRiemannianMetric ThreeModel U)
    (f : ∀ i, bufferedCylinder (δ i) → M) (e : κ ≃ ι) (K : ℝ)
    (hRet : MapsTo (Subtype.val : cutCore f → M)
      (retainedCore f (scalarSublevelComponents U g f K)) U) :
    MapsTo (Subtype.val : cutCore (fun j => f (e j)) → M)
      (retainedCore (fun j => f (e j)) (scalarSublevelComponents U g (fun j => f (e j)) K)) U := by
  intro p hp
  have hi : p.val ∈ (Subtype.val : cutCore f → M) ''
      retainedCore f (scalarSublevelComponents U g f K) := by
    rw [← retainedCore_image_reindex f e U g K]
    exact ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hqp⟩ := hi
  exact hqp ▸ hRet hq

private theorem positive_side_reindex
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]
    {ι : Type v} {κ : Type} {δ : ι → ℝ}
    (U : Opens M) (g : SmoothRiemannianMetric ThreeModel U)
    (f : ∀ i, bufferedCylinder (δ i) → M) (e : κ ≃ ι) (K : ℝ)
    (hδ : ∀ i, 0 < δ i) (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (hside : ∀ i side, cuttingSphereComponent hδ f hf hdisj (i, side) ∈
      scalarSublevelComponents U g f K ↔ side = true) :
    ∀ j side, cuttingSphereComponent (fun j => hδ (e j)) (fun j => f (e j))
      (fun j => hf (e j)) (pairwise_disjoint_reindex f e hdisj) (j, side) ∈
      scalarSublevelComponents U g (fun j => f (e j)) K ↔ side = true := by
  intro j side
  exact (cuttingSphereComponent_mem_reindex f e hδ hf hdisj U g K (j, side)).trans
    (hside (e j) side)

private theorem exists_fin_chosen_data
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]
    {ι : Type v} [Finite ι] {δ : ι → ℝ}
    (U : Opens M) (g : SmoothRiemannianMetric ThreeModel U)
    (f : ∀ i, bufferedCylinder (δ i) → M) (K : ℝ)
    (hδ : ∀ i, 0 < δ i) (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (hRet : MapsTo (Subtype.val : cutCore f → M)
      (retainedCore f (scalarSublevelComponents U g f K)) U)
    (hside : ∀ i side, cuttingSphereComponent hδ f hf hdisj (i, side) ∈
      scalarSublevelComponents U g f K ↔ side = true) :
    ∃ e : Fin (Nat.card ι) ≃ ι,
      let δFin := fun j => δ (e j)
      let fFin : ∀ j, bufferedCylinder (δFin j) → M := fun j => f (e j)
      (∀ j, δFin j = δ (e j)) ∧ (∀ j, fFin j = f (e j)) ∧
      (∀ j, 0 < δFin j) ∧ (∀ j, _root_.Topology.IsOpenEmbedding (fFin j)) ∧
      Pairwise (fun j k => Disjoint (range (fFin j)) (range (fFin k))) ∧
      cutCore fFin = cutCore f ∧
      (Subtype.val : cutCore fFin → M) ''
        retainedCore fFin (scalarSublevelComponents U g fFin K) =
      (Subtype.val : cutCore f → M) ''
        retainedCore f (scalarSublevelComponents U g f K) ∧
      MapsTo (Subtype.val : cutCore fFin → M)
        (retainedCore fFin (scalarSublevelComponents U g fFin K)) U ∧
      ∀ j side, cuttingSphereComponent (fun j => hδ (e j)) fFin
        (fun j => hf (e j)) (pairwise_disjoint_reindex f e hdisj) (j, side) ∈
          scalarSublevelComponents U g fFin K ↔ side = true := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e : Fin (Nat.card ι) ≃ ι :=
    (Fintype.equivFinOfCardEq (Fintype.card_eq_nat_card (α := ι))).symm
  refine ⟨e, ?_⟩
  dsimp only
  refine ⟨fun _ => rfl, fun _ => rfl, fun j => hδ (e j), fun j => hf (e j),
    pairwise_disjoint_reindex f e hdisj, cutCore_reindex f e,
    retainedCore_image_reindex f e U g K,
    retained_terminal_reindex U g f e K hRet, ?_⟩
  exact positive_side_reindex U g f e K hδ hf hdisj hside


private theorem exists_precision_order_compatible {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (m : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ η ∧ ε ≤ δ ∧ ε ≤ 1 / 8646 ∧
      δ⁻¹ + 2 < ε⁻¹ ∧ m + 6 ≤ ⌊ε⁻¹⌋₊ + 1 := by
  let T := max (δ⁻¹ + 3) ((m : ℝ) + 6)
  have hT : 0 < T := lt_of_lt_of_le (by positivity : 0 < δ⁻¹ + 3) (le_max_left _ _)
  let ε := min η (min δ (min (1 / 8646) (1 / (2 * T))))
  have hε : 0 < ε := lt_min hη (lt_min hδ (lt_min (by norm_num) (by positivity)))
  have hεT : ε ≤ 1 / (2 * T) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hTi : T < ε⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hε).mpr
    have hh := mul_le_mul_of_nonneg_left hεT hT.le
    have he : T * (1 / (2 * T)) = 1 / 2 := by field_simp
    rw [he] at hh
    linarith
  refine ⟨ε, hε, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)), ?_, ?_⟩
  · linarith [le_max_left (δ⁻¹ + 3) ((m : ℝ) + 6)]
  · have hm : ((m + 6 : ℕ) : ℝ) ≤ ε⁻¹ := by
      push_cast
      exact (le_max_right (δ⁻¹ + 3) ((m : ℝ) + 6)).trans hTi.le
    exact (Nat.le_floor hm).trans (Nat.le_succ _)

private theorem precision_order_compatible_of_le {δ η ε₀ ε : ℝ} {m : ℕ}
    (hε : 0 < ε) (hle : ε ≤ ε₀) (hη : ε₀ ≤ η) (hδ : ε₀ ≤ δ)
    (hsmall : ε₀ ≤ 1 / 8646) (hwidth : δ⁻¹ + 2 < ε₀⁻¹)
    (horder : m + 6 ≤ ⌊ε₀⁻¹⌋₊ + 1) :
    ε ≤ η ∧ ε ≤ δ ∧ ε ≤ 1 / 8646 ∧ δ⁻¹ + 2 < ε⁻¹ ∧ m + 6 ≤ ⌊ε⁻¹⌋₊ + 1 := by
  have hinv : ε₀⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ (hε.trans_le hle) hε).mpr hle
  exact ⟨hle.trans hη, hle.trans hδ, hle.trans hsmall, hwidth.trans_le hinv,
    horder.trans (Nat.add_le_add_right (Nat.floor_mono hinv) 1)⟩


private theorem exists_finite_oriented_horn_neck_data_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ} (_ : ε ≤ δ) (hδ1 : δ < 1), δ⁻¹ + 2 < ε⁻¹ →
        ∀ m : ℕ, m + 6 ≤ ⌊ε⁻¹⌋₊ + 1 →
        ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
          0 < Q ∧
          ∃ (F : ∀ c, P.hornIndex c →
              NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, P.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (P.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = P.core ∧
            ∃ e : Fin (Nat.card P'.HornCutIndex) ≃ P'.HornCutIndex,
              ∃ (t a : Fin (Nat.card P'.HornCutIndex) → ℝ)
                (ν : Fin (Nat.card P'.HornCutIndex) → Sphere 2 ≃ Sphere 2)
                (x₀ : Fin (Nat.card P'.HornCutIndex) → D.slab.terminalRegularOpen)
                (d : ∀ j : Fin (Nat.card P'.HornCutIndex),
                  normalizedDatum D.terminal.metric (x₀ j) δ (m + 6)),
                (∀ j, 0 < t j ∧ x₀ j = P.horn (e j).1.val (e j).2 (y, t j) ∧
                  metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                (∀ j, δ⁻¹ + 1 < a j) ∧
                (∀ j, (d j).retainedSide = true) ∧
                (∀ j (q : bufferedCylinder δ),
                  (d j).map q = P'.horn (e j).1.val (e j).2
                    (ν j q.val.1, a j - q.val.2)) ∧
                let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
                ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                  (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                  (∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j)) ∧
                  MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                    (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹))
                    D.slab.terminalRegularOpen ∧
                  (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd
                    (j, side) ∈ scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹ ↔ side = true) ∧
                  ∃ (δOriginal : Fin (Nat.card P'.HornCutIndex) → ℝ)
                    (kOriginal : Fin (Nat.card P'.HornCutIndex) → ℕ)
                    (NOriginal : ∀ j, NormalizedNeck D.terminal.metric
                      (δOriginal j) (kOriginal j))
                    (hδOriginal : ∀ j, δOriginal j ≤ δ)
                    (rotation : Fin (Nat.card P'.HornCutIndex) →
                      ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
                    (hmark : ∀ j,
                      DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint =
                      ((NOriginal j).monoDelta (hδOriginal j) hδ1).sphereMark)
                    (side : Fin (Nat.card P'.HornCutIndex) → Bool)
                    (horder : ∀ j, m + 6 ≤ kOriginal j),
                    (∀ j, (NOriginal j).center = x₀ j ∧
                      (NOriginal j).scale = Q ∧ δOriginal j ≤ ε ∧
                      ⌊ε⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
                    (∀ j, LinearMap.det (rotation j).toLinearMap = 1) ∧
                    ∀ j, HEq (d j)
                      ((((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
                        (rotation j) (hmark j) (side j)).oriented.lowerOrder (horder j)) := by
  classical
  obtain ⟨eta, heta, hchoose⟩ := exists_common_scale_oriented_horn_necks_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro D ε Λ P hε δ hεδ hδ1 hfit m hm
  let : SigmaCompactSpace D.slab.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen
        ThreeModel D.slab.terminalRegularOpen.isOpen)
  obtain ⟨Q₀, hQ₀, hfamily⟩ := hchoose P hε hεδ hδ1 hfit
  refine ⟨Q₀, hQ₀, ?_⟩
  intro Q hQ y
  obtain ⟨t, δ₀, k, N, hδ, a, F, K, hK, hfix, hF, hcore, hdata,
    rot, hrot, side, ν, hdet, ha, hmap, hf, hd, hside, hRet⟩ := hfamily Q hQ y
  let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let : Finite P'.component := P'.component_finite.to_subtype
  let (c : P'.component) : Finite (P'.hornIndex c.val) := P'.hornIndex_finite c.val
  let : Finite P'.HornCutIndex := inferInstance
  let Ns := fun j : P'.HornCutIndex => N j.1.val j.2
  let hm' : ∀ j : P'.HornCutIndex, m + 6 ≤ k j.1.val j.2 :=
    fun j => hm.trans (hdata j.1.val j.2).2.2.2.2
  let dHigh := fun j : P'.HornCutIndex =>
    (((Ns j).monoDelta (hδ j.1.val j.2) hδ1).rotatedDatum
      (rot j) (hrot j) (side j)).oriented
  let dLow : ∀ j : P'.HornCutIndex,
      normalizedDatum D.terminal.metric (Ns j).center δ (m + 6) :=
    fun j => (dHigh j).lowerOrder (hm' j)
  obtain ⟨hlowMap, hlowSide, hscalar, _, _, hlocal⟩ :=
    NormalizedNeck.lowerOrder_oriented_rotatedDatum_family
      D.slab.terminalRegularOpen Ns (fun j => hδ j.1.val j.2) hδ1
      rot hrot side hm' (fun j => (hdata j.1.val j.2).2.2.1)
  let fLow := fun j : P'.HornCutIndex =>
    neckAmbientMap D.slab.terminalRegularOpen (dLow j)
  have hfLow : ∀ j, _root_.Topology.IsOpenEmbedding (fLow j) := fun j => hf j
  have hdLow : Pairwise fun i j => Disjoint (range (fLow i)) (range (fLow j)) := hd
  have hRetLow : MapsTo (Subtype.val : cutCore fLow → D.stage.Carrier)
      (retainedCore fLow (scalarSublevelComponents D.slab.terminalRegularOpen
        D.terminal.metric fLow (P'.coreRadius ^ 2)⁻¹)) D.slab.terminalRegularOpen := hRet
  have hsideLow : ∀ j s, cuttingSphereComponent (fun j => (dLow j).precision_pos)
      fLow hfLow hdLow (j, s) ∈
        scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric fLow
          (P'.coreRadius ^ 2)⁻¹ ↔ s = true := hside
  obtain ⟨e, _, _, _, hfFin, hdFin, _, _, hRetFin, hsideFin⟩ :=
    exists_fin_chosen_data D.slab.terminalRegularOpen D.terminal.metric fLow
      (P'.coreRadius ^ 2)⁻¹ (fun j => (dLow j).precision_pos) hfLow hdLow hRetLow hsideLow
  refine ⟨hQ₀.trans hQ, F, K, hK, hfix, hF, hcore, e,
    (fun j => t (e j).1.val (e j).2), (fun j => a (e j).1.val (e j).2),
    ν ∘ e, (fun j => (Ns (e j)).center), (fun j => dLow (e j)), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨(hdata (e j).1.val (e j).2).1,
      (hdata (e j).1.val (e j).2).2.1, hscalar (e j)⟩
  · intro j
    exact ha (e j).1.val (e j).2
  · intro j
    exact hlowSide (e j)
  · intro j q
    change (dLow (e j)).map q = _
    calc
      (dLow (e j)).map q = (dHigh (e j)).map q := congrFun (hlowMap (e j)) q
      _ = _ := hmap (e j) q
  · refine ⟨hfFin, hdFin, ?_, hRetFin, ?_, ?_⟩
    · intro j
      exact hlocal (e j)
    · intro j s
      exact hsideFin j s
    · refine ⟨(fun j => δ₀ (e j).1.val (e j).2),
        (fun j => k (e j).1.val (e j).2), (fun j => Ns (e j)),
        (fun j => hδ (e j).1.val (e j).2), (fun j => rot (e j)),
        (fun j => hrot (e j)), (fun j => side (e j)), (fun j => hm' (e j)),
        ?_, ?_, ?_⟩
      · intro j
        exact ⟨rfl, (hdata (e j).1.val (e j).2).2.2.1,
          (hdata (e j).1.val (e j).2).2.2.2.1,
          (hdata (e j).1.val (e j).2).2.2.2.2⟩
      · intro j
        exact hdet (e j)
      · intro j
        exact HEq.rfl


theorem exists_uniform_horn_cut_metricCutCapEvent_volume_debit_with_recenter_data :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
      ∃ δ : ℝ, 0 < δ ∧ ∃ hquarter : δ < 1 / 4, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      2 * ⌊δ⁻¹⌋₊ + 4 ≤ ⌊ε₀⁻¹⌋₊ + 1 ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
      ε ≤ ε₀ → ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
          ∃ (F : ∀ c, P.hornIndex c →
              NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, P.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (P.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = P.core ∧
            ∃ e : Fin (Nat.card P'.HornCutIndex) ≃ P'.HornCutIndex,
              ∃ (t a : Fin (Nat.card P'.HornCutIndex) → ℝ)
                (ν : Fin (Nat.card P'.HornCutIndex) → Sphere 2 ≃ Sphere 2)
                (x₀ : Fin (Nat.card P'.HornCutIndex) → D.slab.terminalRegularOpen)
                (d : ∀ j : Fin (Nat.card P'.HornCutIndex),
                  normalizedDatum D.terminal.metric (x₀ j) δ (m + 6)),
                (∀ j, 0 < t j ∧ x₀ j = P.horn (e j).1.val (e j).2 (y, t j) ∧
                  metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                (∀ j, δ⁻¹ + 1 < a j) ∧
                (∀ j, (d j).retainedSide = true) ∧
                (∀ j (q : bufferedCylinder δ),
                  (d j).map q = P'.horn (e j).1.val (e j).2
                    (ν j q.val.1, a j - q.val.2)) ∧
                let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
                ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                  (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                  ∃ hlocal : ∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j),
                  ∃ hRet : MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                    (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹))
                    D.slab.terminalRegularOpen,
                  (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd
                    (j, side) ∈ scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹ ↔ side = true) ∧
                  (∃ (δOriginal : Fin (Nat.card P'.HornCutIndex) → ℝ)
                    (kOriginal : Fin (Nat.card P'.HornCutIndex) → ℕ)
                    (NOriginal : ∀ j, NormalizedNeck D.terminal.metric
                      (δOriginal j) (kOriginal j))
                    (hδOriginal : ∀ j, δOriginal j ≤ δ)
                    (rotation : Fin (Nat.card P'.HornCutIndex) →
                      ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
                    (hmark : ∀ j,
                      DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint =
                      ((NOriginal j).monoDelta (hδOriginal j)
                        (hquarter.trans (by norm_num))).sphereMark)
                    (side : Fin (Nat.card P'.HornCutIndex) → Bool)
                    (horder : ∀ j, m + 6 ≤ kOriginal j),
                    (∀ j, (NOriginal j).center = x₀ j ∧
                      (NOriginal j).scale = Q ∧ δOriginal j ≤ ε ∧
                      ⌊ε⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
                    (∀ j, LinearMap.det (rotation j).toLinearMap = 1) ∧
                    ∀ j, HEq (d j)
                      ((((NOriginal j).monoDelta (hδOriginal j)
                        (hquarter.trans (by norm_num))).rotatedDatum
                        (rotation j) (hmark j) (side j)).oriented.lowerOrder (horder j))) ∧
                  let R := scalarSublevelComponents D.slab.terminalRegularOpen
                    D.terminal.metric f (P'.coreRadius ^ 2)⁻¹
      let hnontrivial :=
        D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f R hRet
      let Bidx := {b : Fin (Nat.card P'.HornCutIndex) × Bool //
        cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd b ∈ R}
      let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos)
        f (fun i => (hf i).injective) hd
      letI : SecondCountableTopology D.stage.Carrier :=
        ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace D.stage.Carrier
      letI : SigmaCompactSpace D.slab.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      D.slab.terminalRegularOpen.isOpen)
      letI : LocallyPathConnectedSpace D.stage.Carrier :=
        originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      letI : ChartedSpace ThreeSpace Qcap :=
        finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd
      letI : IsManifold ThreeModel ∞ Qcap :=
        finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd hlocal
      letI : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos
        (fun j => (d j).precision_pos) f hf hd
      letI : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos
        (fun j => (d j).precision_pos) f hf hd
      letI : CompactSpace Ret :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd R).1
      letI : CompactSpace Disc :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd R).2
      ∃ (oQ : SmoothOrientation ThreeModel Qcap) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (rotationCap : (Fin (Nat.card P'.HornCutIndex) × Bool) → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (B : (Fin (Nat.card P'.HornCutIndex) × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (aCap : (Fin (Nat.card P'.HornCutIndex) × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (aCap b y)),
        (∀ b, rotationCap b = LinearIsometryEquiv.refl ℝ ThreeSpace ∨
          rotationCap b = LinearIsometryEquiv.neg ℝ) ∧
        (∀ b x, (B b x : ThreeSpace) = rotationCap b x) ∧
      ∃ E : MetricCutCapEvent D.stage
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) D.startTime D.endTime,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Qcap oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos (fun j => (d j).precision_pos)
            (fun i => (d i).precision_lt_one) f hf hd R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (aCap b).toHomeomorph) hboundary) ∧
        E.transition.trace.tubes = TubeSystem.ofBufferedCharts (fun j => (d j).precision_pos)
          (fun i => (d i).precision_lt_one) f hf hd ∧
        E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel
            (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier
            E.outputMetric univ + ENNReal.ofReal
              ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
      ∃ hrec : ∀ _ : Bidx, (c * δ)⁻¹ + 1 ≤ (δ)⁻¹,
      ∃ dCap : ∀ b : Bidx, normalizedDatum D.terminal.metric
        ((d b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * δ) (m + 4),
      ∃ hmap : ∀ b : Bidx, (dCap b).map =
        (d b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (dCap b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (dCap b) A hA Dcap m accuracy,
        E.outputMetric = finiteFullPreparedMetric ThreeModel
          (fun j => (d j).precision_pos) f hf hd hlocal
          D.slab.terminalRegularOpen D.terminal.metric R hRet c hc x₀ (fun _ => m + 6) d
          (fun _ => rfl) hrec dCap hmap hside w ∧
        (∀ b : Bidx, |metricScalarAt D.terminal.metric
          ((d b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
            metricScalarAt D.terminal.metric (x₀ b.val.1) - 1| ≤ c * δ) ∧
        (∀ b : Bidx, StaticInsertionAdditionalProperties C (w b)) ∧
        ∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q := by
  classical
  choose c hc C hC A hA hsmall hfactory using
    exists_uniform_metricCutCapEvent_volume_debit_with_recenter_data.{u}
  choose δcap hδcap hcapHalf hcapScalar using
    exists_metricCutCapEvent_capRegion_scalar_lower A hA
  choose eta heta hchoose using exists_finite_oriented_horn_neck_data_tolerance.{u}
  apply Exists.intro c
  apply Exists.intro hc
  apply Exists.intro C
  apply And.intro hC
  apply Exists.intro A
  apply Exists.intro hA
  apply And.intro hsmall.1
  intro Dcap hDcap m accuracy haccuracy
  have choice := hfactory Dcap hDcap m accuracy haccuracy δcap hδcap
  let δ : ℝ := Classical.choose choice
  have hδ := (Classical.choose_spec choice).1
  have hquarter := (Classical.choose_spec choice).2.1
  choose εbase hεbase hεeta hεδ hεsmall hwidth horder using
    exists_precision_order_compatible hδ heta m
  let ε₀ := min εbase (((2 * ⌊δ⁻¹⌋₊ + 4 : ℕ) : ℝ))⁻¹
  have hε₀ : 0 < ε₀ := lt_min hεbase (by positivity)
  have hεorder : 2 * ⌊δ⁻¹⌋₊ + 4 ≤ ⌊ε₀⁻¹⌋₊ + 1 := by
    have hle : ((2 * ⌊δ⁻¹⌋₊ + 4 : ℕ) : ℝ) ≤ ε₀⁻¹ := by
      simpa only [inv_inv] using inv_anti₀ hε₀ (min_le_right εbase
        (((2 * ⌊δ⁻¹⌋₊ + 4 : ℕ) : ℝ))⁻¹)
    exact (Nat.le_floor hle).trans (Nat.le_succ _)
  apply Exists.intro δ
  apply And.intro hδ
  apply Exists.intro hquarter
  apply Exists.intro ε₀
  apply And.intro hε₀
  apply And.intro hεorder
  intro D ε Λ P hε
  have hcompat := precision_order_compatible_of_le P.epsilon_pos
    (hε.trans (min_le_left _ _)) hεeta hεδ hεsmall hwidth horder
  have choiceQ := hchoose P hcompat.1 hcompat.2.1 (hquarter.trans (by norm_num))
    hcompat.2.2.2.1 m hcompat.2.2.2.2
  let Q₀ : ℝ := Classical.choose choiceQ
  have hQ₀ := (Classical.choose_spec choiceQ).1
  apply Exists.intro Q₀
  apply And.intro hQ₀
  intro Q hQ y
  choose hQpos F K hK hfix hF hcore e t a ν x₀ d hcenter ha hside hmap hf hd hlocal hRet
    hfaces horiginal using
    (Classical.choose_spec choiceQ).2 Q hQ y
  let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
  let R := scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
    (P'.coreRadius ^ 2)⁻¹
  have hone (j) : cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,true) ∈ R ∧
      cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,false) ∉ R := by
    exact ⟨(hfaces j true).mpr rfl,fun h => Bool.false_ne_true ((hfaces j false).mp h)⟩
  have hevent := (Classical.choose_spec choice).2.2 D.slab D.terminal (fun _ => δ)
    (fun j => (d j).precision_pos)
    (fun _ => le_rfl) x₀ d f hf hd hlocal (fun _ => rfl) R hRet D.singular hone
    Q hQpos (fun j => (hcenter j).2.2)
  let hnontrivial := D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f R hRet
  let Bidx := {b : Fin (Nat.card P'.HornCutIndex) × Bool //
    cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd b ∈ R}
  let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos)
    f (fun j => (hf j).injective) hd
  let : LocallyPathConnectedSpace D.stage.Carrier :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd
  let : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd hlocal
  let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).2
  choose oQ oRet oDisc rotationCap B aCap hboundary hchoice hB E hDisc hCap htrace htubes hG hL hOld hBoundary
    hpin hfloor hvol hrec dCap hcapMap hcapSide w hOutput hratio hw hcapPrecision hlow using hevent
  have hcapMake := hcapScalar (fun j => (d j).precision_pos) (fun j => (d j).precision_lt_one)
    f hf hd hlocal R hnontrivial
    (t₀ := D.startTime) (t₁ := D.endTime) (D := Dcap) (ε := accuracy) (m := m)
  have hbound := hcapMake oQ oRet oDisc E (fun b => (B b).toHomeomorph)
    (fun b => (aCap b).toHomeomorph) hboundary hDisc hCap htrace
    D.slab.terminalRegularOpen D.terminal.metric hRet c hc x₀ (fun _ => m + 6) d
    (fun _ => rfl) (fun _ => m + 4) hrec dCap hcapMap hcapSide w
    hcapPrecision (fun _ => by omega) (Q / 2) hlow hOutput
  have hbound' : ∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q := by
    intro q hq
    convert hbound q hq using 1
    ring
  refine ⟨F,K,hK,hfix,hF,hcore,e,t,a,ν,x₀,d,hcenter,ha,hside,hmap,
    hf,hd,hlocal,hRet,hfaces,horiginal,?_⟩
  exact ⟨oQ,oRet,oDisc,rotationCap,B,aCap,hboundary,hchoice,hB,E,hDisc,hCap,htrace,htubes,hG,hL,hOld,hBoundary,
    hpin,hfloor,hvol,hrec,dCap,hcapMap,hcapSide,w,hOutput,hratio,hw,hbound'⟩


theorem exists_uniform_horn_cut_metricCutCapEvent_volume_debit_cap_scalar_lower :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
      ∃ δ : ℝ, 0 < δ ∧ ∃ hquarter : δ < 1 / 4, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
      ε ≤ ε₀ → ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
          ∃ (F : ∀ c, P.hornIndex c →
              NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, P.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (P.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = P.core ∧
            ∃ e : Fin (Nat.card P'.HornCutIndex) ≃ P'.HornCutIndex,
              ∃ (t a : Fin (Nat.card P'.HornCutIndex) → ℝ)
                (ν : Fin (Nat.card P'.HornCutIndex) → Sphere 2 ≃ Sphere 2)
                (x₀ : Fin (Nat.card P'.HornCutIndex) → D.slab.terminalRegularOpen)
                (d : ∀ j : Fin (Nat.card P'.HornCutIndex),
                  normalizedDatum D.terminal.metric (x₀ j) δ (m + 6)),
                (∀ j, 0 < t j ∧ x₀ j = P.horn (e j).1.val (e j).2 (y, t j) ∧
                  metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                (∀ j, δ⁻¹ + 1 < a j) ∧
                (∀ j, (d j).retainedSide = true) ∧
                (∀ j (q : bufferedCylinder δ),
                  (d j).map q = P'.horn (e j).1.val (e j).2
                    (ν j q.val.1, a j - q.val.2)) ∧
                let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
                ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                  (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                  ∃ hlocal : ∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j),
                  ∃ hRet : MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                    (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹))
                    D.slab.terminalRegularOpen,
                  (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd
                    (j, side) ∈ scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹ ↔ side = true) ∧
                  (∃ (δOriginal : Fin (Nat.card P'.HornCutIndex) → ℝ)
                    (kOriginal : Fin (Nat.card P'.HornCutIndex) → ℕ)
                    (NOriginal : ∀ j, NormalizedNeck D.terminal.metric
                      (δOriginal j) (kOriginal j))
                    (hδOriginal : ∀ j, δOriginal j ≤ δ)
                    (rotation : Fin (Nat.card P'.HornCutIndex) →
                      ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
                    (hmark : ∀ j,
                      DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j) spherePoint =
                      ((NOriginal j).monoDelta (hδOriginal j)
                        (hquarter.trans (by norm_num))).sphereMark)
                    (side : Fin (Nat.card P'.HornCutIndex) → Bool)
                    (horder : ∀ j, m + 6 ≤ kOriginal j),
                    (∀ j, (NOriginal j).center = x₀ j ∧
                      (NOriginal j).scale = Q ∧ δOriginal j ≤ ε ∧
                      ⌊ε⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
                    (∀ j, LinearMap.det (rotation j).toLinearMap = 1) ∧
                    ∀ j, HEq (d j)
                      ((((NOriginal j).monoDelta (hδOriginal j)
                        (hquarter.trans (by norm_num))).rotatedDatum
                        (rotation j) (hmark j) (side j)).oriented.lowerOrder (horder j))) ∧
                  let R := scalarSublevelComponents D.slab.terminalRegularOpen
                    D.terminal.metric f (P'.coreRadius ^ 2)⁻¹
      let hnontrivial :=
        D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f R hRet
      let Bidx := {b : Fin (Nat.card P'.HornCutIndex) × Bool //
        cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd b ∈ R}
      let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos)
        f (fun i => (hf i).injective) hd
      letI : SecondCountableTopology D.stage.Carrier :=
        ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace D.stage.Carrier
      letI : SigmaCompactSpace D.slab.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      D.slab.terminalRegularOpen.isOpen)
      letI : LocallyPathConnectedSpace D.stage.Carrier :=
        originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      letI : ChartedSpace ThreeSpace Qcap :=
        finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd
      letI : IsManifold ThreeModel ∞ Qcap :=
        finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd hlocal
      letI : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos
        (fun j => (d j).precision_pos) f hf hd
      letI : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos
        (fun j => (d j).precision_pos) f hf hd
      letI : CompactSpace Ret :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd R).1
      letI : CompactSpace Disc :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos
          (fun j => (d j).precision_pos) f hf hd R).2
      ∃ (oQ : SmoothOrientation ThreeModel Qcap) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (B : (Fin (Nat.card P'.HornCutIndex) × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (aCap : (Fin (Nat.card P'.HornCutIndex) × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (aCap b y)),
      ∃ E : MetricCutCapEvent D.stage
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) D.startTime D.endTime,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Qcap oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos (fun j => (d j).precision_pos)
            (fun i => (d i).precision_lt_one) f hf hd R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (aCap b).toHomeomorph) hboundary) ∧
        E.transition.trace.tubes = TubeSystem.ofBufferedCharts (fun j => (d j).precision_pos)
          (fun i => (d i).precision_lt_one) f hf hd ∧
        E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel
            (OrientedThreeStage.ofSmoothOrientation Ret oRet).Carrier
            E.outputMetric univ + ENNReal.ofReal
              ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
      ∃ hrec : ∀ _ : Bidx, (c * δ)⁻¹ + 1 ≤ (δ)⁻¹,
      ∃ dCap : ∀ b : Bidx, normalizedDatum D.terminal.metric
        ((d b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * δ) (m + 4),
      ∃ hmap : ∀ b : Bidx, (dCap b).map =
        (d b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (dCap b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (dCap b) A hA Dcap m accuracy,
        E.outputMetric = finiteFullPreparedMetric ThreeModel
          (fun j => (d j).precision_pos) f hf hd hlocal
          D.slab.terminalRegularOpen D.terminal.metric R hRet c hc x₀ (fun _ => m + 6) d
          (fun _ => rfl) hrec dCap hmap hside w ∧
        (∀ b : Bidx, StaticInsertionAdditionalProperties C (w b)) ∧
        ∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q := by
  classical
  choose c hc C hC A hA hsmall hfamily using
    exists_uniform_horn_cut_metricCutCapEvent_volume_debit_with_recenter_data.{u}
  refine ⟨c, hc, C, hC, A, hA, hsmall, ?_⟩
  intro Dcap hDcap m accuracy haccuracy
  choose δ hδ hquarter ε₀ hε₀ hεorder hmake using hfamily Dcap hDcap m accuracy haccuracy
  refine ⟨δ, hδ, hquarter, ε₀, hε₀, ?_⟩
  intro D ε Λ P hε
  choose Q₀ hQ₀ hmakeQ using hmake P hε
  refine ⟨Q₀, hQ₀, ?_⟩
  intro Q hQ y
  choose F K hK hfix hF hcore e t a ν x₀ d hcenter ha hside hmap hf hd hlocal hRet
    hfaces horiginal oQ oRet oDisc rotationCap B aCap hboundary hchoice hB E
    hDisc hCap htrace htubes hG hL hOld hBoundary hpin hfloor hvol hrec dCap
    hcapMap hcapSide w hOutput hratio hw hbound using hmakeQ Q hQ y
  exact ⟨F, K, hK, hfix, hF, hcore, e, t, a, ν, x₀, d, hcenter, ha, hside, hmap,
    hf, hd, hlocal, hRet, hfaces, horiginal, oQ, oRet, oDisc, B, aCap, hboundary,
    E, hDisc, hCap, htrace, htubes, hG, hL, hOld, hBoundary, hpin, hfloor, hvol,
    hrec, dCap, hcapMap, hcapSide, w, hOutput, hw, hbound⟩

theorem exists_uniform_horn_cut_metricCutCapEvent_volume_debit_with_neck :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
      ∃ δ : ℝ, 0 < δ ∧ ∃ hquarter : δ < 1 / 4, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
      ε ≤ ε₀ → ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
          ∃ (F : ∀ c, P.hornIndex c →
              NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, P.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (P.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = P.core ∧
            ∃ e : Fin (Nat.card P'.HornCutIndex) ≃ P'.HornCutIndex,
              ∃ (t a : Fin (Nat.card P'.HornCutIndex) → ℝ)
                (ν : Fin (Nat.card P'.HornCutIndex) → Sphere 2 ≃ Sphere 2)
                (x₀ : Fin (Nat.card P'.HornCutIndex) → D.slab.terminalRegularOpen)
                (d : ∀ j : Fin (Nat.card P'.HornCutIndex),
                  normalizedDatum D.terminal.metric (x₀ j) δ (m + 6)),
                (∀ j, 0 < t j ∧ x₀ j = P.horn (e j).1.val (e j).2 (y, t j) ∧
                  metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                (∀ j, δ⁻¹ + 1 < a j) ∧
                (∀ j, (d j).retainedSide = true) ∧
                (∀ j (q : bufferedCylinder δ),
                  (d j).map q = P'.horn (e j).1.val (e j).2
                    (ν j q.val.1, a j - q.val.2)) ∧
                let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
                ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                  (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                  ∃ hlocal : ∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j),
                  ∃ hRet : MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                    (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹))
                    D.slab.terminalRegularOpen,
                  (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd
                    (j, side) ∈ scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹ ↔ side = true) ∧
                  (∃ (δOriginal : Fin (Nat.card P'.HornCutIndex) → ℝ)
                    (kOriginal : Fin (Nat.card P'.HornCutIndex) → ℕ)
                    (NOriginal : ∀ j, NormalizedNeck D.terminal.metric
                      (δOriginal j) (kOriginal j))
                    (hδOriginal : ∀ j, δOriginal j ≤ δ)
                    (rotation : Fin (Nat.card P'.HornCutIndex) →
                      ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
                    (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation
                      j) spherePoint =
                      ((NOriginal j).monoDelta (hδOriginal j) (hquarter.trans (by
                        norm_num))).sphereMark)
                    (side : Fin (Nat.card P'.HornCutIndex) → Bool)
                    (horder : ∀ j, m + 6 ≤ kOriginal j),
                    (∀ j, (NOriginal j).center = x₀ j ∧
                      (NOriginal j).scale = Q ∧ δOriginal j ≤ ε ∧
                      ⌊ε⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
                    (∀ j, LinearMap.det (rotation j).toLinearMap = 1) ∧
                    ∀ j, HEq (d j)
                      ((((NOriginal j).monoDelta (hδOriginal j) (hquarter.trans (by
                        norm_num))).rotatedDatum
                        (rotation j) (hmark j) (side j)).oriented.lowerOrder (horder j))) ∧
                  let R := scalarSublevelComponents D.slab.terminalRegularOpen
                    D.terminal.metric f (P'.coreRadius ^ 2)⁻¹
      let hnontrivial := D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f
        R hRet
      let Bidx := {b : Fin (Nat.card P'.HornCutIndex) × Bool // cuttingSphereComponent (fun j
        => (d j).precision_pos) f hf hd b ∈ R}
      let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos) f (fun i
        => (hf i).injective) hd
      letI : SecondCountableTopology D.stage.Carrier :=
        ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace D.stage.Carrier
      letI : SigmaCompactSpace D.slab.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
          D.slab.terminalRegularOpen.isOpen)
      letI : LocallyPathConnectedSpace D.stage.Carrier :=
        originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      letI : ChartedSpace ThreeSpace Qcap :=
        finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos (fun j
          => (d j).precision_pos) f hf hd
      letI : IsManifold ThreeModel ∞ Qcap :=
        finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d
          j).precision_pos) f hf hd hlocal
      letI : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos (fun j => (d
        j).precision_pos) f hf hd
      letI : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos (fun j => (d
        j).precision_pos) f hf hd
      letI : CompactSpace Ret :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos (fun j => (d
          j).precision_pos) f hf hd R).1
      letI : CompactSpace Disc :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos (fun j => (d
          j).precision_pos) f hf hd R).2
      ∃ (oQ : SmoothOrientation ThreeModel Qcap) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (B : (Fin (Nat.card P'.HornCutIndex) × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (aCap : (Fin (Nat.card P'.HornCutIndex) × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (aCap b y)),
      ∃ E : MetricCutCapEvent D.stage
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) D.startTime D.endTime,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Qcap oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos (fun j => (d j).precision_pos)
            (fun i => (d i).precision_lt_one) f hf hd R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (aCap b).toHomeomorph) hboundary) ∧
        E.transition.trace.tubes = TubeSystem.ofBufferedCharts (fun j => (d j).precision_pos)
          (fun i => (d i).precision_lt_one) f hf hd ∧
        E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel (OrientedThreeStage.ofSmoothOrientation Ret
            oRet).Carrier
            E.outputMetric univ + ENNReal.ofReal
              ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
      ∃ hrec : ∀ _ : Bidx, (c * δ)⁻¹ + 1 ≤ (δ)⁻¹,
      ∃ dCap : ∀ b : Bidx, normalizedDatum D.terminal.metric
        ((d b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * δ) (m + 4),
      ∃ hmap : ∀ b : Bidx, (dCap b).map =
        (d b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (dCap b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (dCap b) A hA Dcap m accuracy,
        E.outputMetric = finiteFullPreparedMetric ThreeModel (fun j => (d j).precision_pos) f
          hf hd hlocal
          D.slab.terminalRegularOpen D.terminal.metric R hRet c hc x₀ (fun _ => m + 6) d
          (fun _ => rfl) hrec dCap hmap hside w ∧
        ∀ b : Bidx, StaticInsertionAdditionalProperties C (w b) := by
  classical
  choose c hc C hC A hA hsmall hfamily using
    exists_uniform_horn_cut_metricCutCapEvent_volume_debit_cap_scalar_lower.{u}
  refine ⟨c,hc,C,hC,A,hA,hsmall,?_⟩
  intro Dcap hDcap m accuracy haccuracy
  choose δ hδ hquarter ε₀ hε₀ hp using hfamily Dcap hDcap m accuracy haccuracy
  refine ⟨δ,hδ,hquarter,ε₀,hε₀,?_⟩
  intro D ε Λ P hε
  choose Q₀ hQ₀ hQ using hp P hε
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQlt y
  choose F K hK hfix hF hcore e t a ν x₀ d hcenter ha hside hmap hf hd hlocal hRet
    hfaces horiginal hevent using hQ Q hQlt y
  let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
  let R := scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
    (P'.coreRadius ^ 2)⁻¹
  let hnontrivial := D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f R hRet
  let Bidx := {b : Fin (Nat.card P'.HornCutIndex) × Bool //
    cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd b ∈ R}
  let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos)
    f (fun j => (hf j).injective) hd
  let : LocallyPathConnectedSpace D.stage.Carrier :=
    originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
  let : ChartedSpace ThreeSpace Qcap := finiteCapChartedSpace ThreeModel
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd
  let : IsManifold ThreeModel ∞ Qcap := finiteCapQuotient_isManifold
    finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d j).precision_pos) f hf hd hlocal
  let : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd
  let : CompactSpace Ret := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).1
  let : CompactSpace Disc := (finiteCapRetained_discarded_compactSpace transitionEnd_pos
    (fun j => (d j).precision_pos) f hf hd R).2
  choose oQ oRet oDisc B aCap hboundary E hDisc hCap htrace htubes hG hL hOld hBoundary
    hpin hfloor hvol hrec dCap hcapMap hcapSide w hOutput hw hcapScalar using hevent
  refine ⟨F,K,hK,hfix,hF,hcore,e,t,a,ν,x₀,d,hcenter,ha,hside,hmap,
    hf,hd,hlocal,hRet,hfaces,horiginal,?_⟩
  exact ⟨oQ,oRet,oDisc,B,aCap,hboundary,E,hDisc,hCap,htrace,htubes,hG,hL,hOld,hBoundary,
    hpin,hfloor,hvol,hrec,dCap,hcapMap,hcapSide,w,hOutput,hw⟩

theorem exists_uniform_horn_cut_metricCutCapEvent_volume_debit :
    ∃ (c : ℝ) (hc : 4 ≤ c), ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
      ε ≤ ε₀ → ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
          ∃ (F : ∀ c, P.hornIndex c →
              NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, P.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder),
              q.2 ≤ (P.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, EqOn (F c e) id (K c e)ᶜ),
            let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = P.core ∧
            ∃ e : Fin (Nat.card P'.HornCutIndex) ≃ P'.HornCutIndex,
              ∃ (t a : Fin (Nat.card P'.HornCutIndex) → ℝ)
                (ν : Fin (Nat.card P'.HornCutIndex) → Sphere 2 ≃ Sphere 2)
                (x₀ : Fin (Nat.card P'.HornCutIndex) → D.slab.terminalRegularOpen)
                (d : ∀ j : Fin (Nat.card P'.HornCutIndex),
                  normalizedDatum D.terminal.metric (x₀ j) δ (m + 6)),
                (∀ j, 0 < t j ∧ x₀ j = P.horn (e j).1.val (e j).2 (y, t j) ∧
                  metricScalarAt D.terminal.metric (x₀ j) = Q) ∧
                (∀ j, δ⁻¹ + 1 < a j) ∧
                (∀ j, (d j).retainedSide = true) ∧
                (∀ j (q : bufferedCylinder δ),
                  (d j).map q = P'.horn (e j).1.val (e j).2
                    (ν j q.val.1, a j - q.val.2)) ∧
                let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j)
                ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                  (hd : Pairwise fun i j => Disjoint (range (f i)) (range (f j))),
                  ∃ hlocal : ∀ j, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (f j),
                  ∃ hRet : MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                    (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹))
                    D.slab.terminalRegularOpen,
                  (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd
                    (j, side) ∈ scalarSublevelComponents D.slab.terminalRegularOpen
                      D.terminal.metric f (P'.coreRadius ^ 2)⁻¹ ↔ side = true) ∧
                  let R := scalarSublevelComponents D.slab.terminalRegularOpen
                    D.terminal.metric f (P'.coreRadius ^ 2)⁻¹
      let hnontrivial := D.slab.nonempty_cut_or_discardedCore_of_singularEndpoint D.singular f
        R hRet
      let Bidx := {b : Fin (Nat.card P'.HornCutIndex) × Bool // cuttingSphereComponent (fun j
        => (d j).precision_pos) f hf hd b ∈ R}
      let Qcap := FiniteCapQuotient transitionEnd_pos (fun j => (d j).precision_pos) f (fun i
        => (hf i).injective) hd
      letI : SecondCountableTopology D.stage.Carrier :=
        ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace D.stage.Carrier
      letI : SigmaCompactSpace D.slab.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
          D.slab.terminalRegularOpen.isOpen)
      letI : LocallyPathConnectedSpace D.stage.Carrier :=
        originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
      let Ret := finiteCapRetained transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      let Disc := finiteCapDiscarded transitionEnd_pos (fun j => (d j).precision_pos) f hf hd R
      letI : ChartedSpace ThreeSpace Qcap :=
        finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three transitionEnd_pos (fun j
          => (d j).precision_pos) f hf hd
      letI : IsManifold ThreeModel ∞ Qcap :=
        finiteCapQuotient_isManifold finrank_threeSpace_eq_three transitionEnd_pos (fun j => (d
          j).precision_pos) f hf hd hlocal
      letI : T2Space Qcap := finiteCapQuotient_t2Space transitionEnd_pos (fun j => (d
        j).precision_pos) f hf hd
      letI : CompactSpace Qcap := finiteCapQuotient_compactSpace transitionEnd_pos (fun j => (d
        j).precision_pos) f hf hd
      letI : CompactSpace Ret :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos (fun j => (d
          j).precision_pos) f hf hd R).1
      letI : CompactSpace Disc :=
        (finiteCapRetained_discarded_compactSpace transitionEnd_pos (fun j => (d
          j).precision_pos) f hf hd R).2
      ∃ (oQ : SmoothOrientation ThreeModel Qcap) (oRet : SmoothOrientation ThreeModel Ret)
        (oDisc : SmoothOrientation ThreeModel Disc)
        (B : (Fin (Nat.card P'.HornCutIndex) × Bool) → ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
        (aCap : (Fin (Nat.card P'.HornCutIndex) × Bool) → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
        (hboundary : ∀ b y, B b (sphereToThreeBall y) = sphereToThreeBall (aCap b y)),
      ∃ E : MetricCutCapEvent D.stage
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) D.startTime D.endTime,
        E.discarded = OrientedThreeStage.ofSmoothOrientation Disc oDisc ∧
        E.capped = OrientedThreeStage.ofSmoothOrientation Qcap oQ ∧
        HEq E.transition.trace
          ((CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos (fun j => (d j).precision_pos)
            (fun i => (d i).precision_lt_one) f hf hd R hnontrivial).reparametrizeCaps
              (fun b => (B b).toHomeomorph) (fun b => (aCap b).toHomeomorph) hboundary) ∧
        E.transition.trace.tubes = TubeSystem.ofBufferedCharts (fun j => (d j).precision_pos)
          (fun i => (d i).precision_lt_one) f hf hd ∧
        E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.old = E.transition.trace.retainedCore ∧ E.transition.boundaryFrameReversing ∧
        (∀ a : ℝ, 0 < a →
          (∀ x : E.incoming.terminalRegularOpen, InFixedHamiltonIveyRegion E.terminal.metric a x) →
          ∀ x : Ret, InFixedHamiltonIveyRegion E.outputMetric a x) ∧
        (∀ L₀ : ℝ, L₀ ≤ 0 →
          (∀ x : E.incoming.terminalRegularOpen, L₀ ≤ metricScalarAt E.terminal.metric x) →
          ∀ x : Ret, L₀ ≤ metricScalarAt E.outputMetric x) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel (OrientedThreeStage.ofSmoothOrientation Ret
            oRet).Carrier
            E.outputMetric univ + ENNReal.ofReal
              ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
      ∃ hrec : ∀ _ : Bidx, (c * δ)⁻¹ + 1 ≤ (δ)⁻¹,
      ∃ dCap : ∀ b : Bidx, normalizedDatum D.terminal.metric
        ((d b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * δ) (m + 4),
      ∃ hmap : ∀ b : Bidx, (dCap b).map =
        (d b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b),
      ∃ hside : ∀ b : Bidx, (dCap b).retainedSide = true,
      ∃ w : ∀ b : Bidx, CanonicalStaticInsertionWitness (dCap b) A hA Dcap m accuracy,
        E.outputMetric = finiteFullPreparedMetric ThreeModel (fun j => (d j).precision_pos) f
          hf hd hlocal
          D.slab.terminalRegularOpen D.terminal.metric R hRet c hc x₀ (fun _ => m + 6) d
          (fun _ => rfl) hrec dCap hmap hside w ∧
        ∀ b : Bidx, StaticInsertionAdditionalProperties C (w b) := by
  classical
  choose c hc C hC A hA hsmall hfamily using
    exists_uniform_horn_cut_metricCutCapEvent_volume_debit_with_neck.{u}
  refine ⟨c,hc,C,hC,A,hA,hsmall,?_⟩
  intro Dcap hDcap m accuracy haccuracy
  choose δ hδ hquarter ε₀ hε₀ hp using hfamily Dcap hDcap m accuracy haccuracy
  refine ⟨δ,hδ,hquarter,ε₀,hε₀,?_⟩
  intro D ε Λ P hε
  choose Q₀ hQ₀ hQ using hp P hε
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQQ y
  choose F K hK hfix hF hcore e t a ν x₀ d hcenter ha hside hmap hf hd hlocal hRet hfaces
    horiginal hevent using
    hQ Q hQQ y
  exact ⟨F,K,hK,hfix,hF,hcore,e,t,a,ν,x₀,d,hcenter,ha,hside,hmap,hf,hd,hlocal,hRet,hfaces,hevent⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
