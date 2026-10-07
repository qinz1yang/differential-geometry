import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ImageVolumeLower_S100
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickRadiusTransfer_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterGap_O7
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps

set_option autoImplicit false

/-! # CH12-S100 G2: the volume witness `hvolw` of `exists_disjoint_family_of_steps_O41`.

* `post_vol_univ_eq_S100`: total volume of `postStage t` for the normalised metric = `normalizedTotalVolume_S13`
  of the regular slice at `t` (transport along `postStage_regularSlice` / `postMetric_regularSlice`).
* `core_image_S100`: for one model datum (the S4 conjuncts), the image of the model ball `B(x, 2)` at a late time is
  open, lies in the image of the slice, and has normalised volume `≥ (2/3) ballVolume (B(x,2))` (G1).
* `hvolw_S100`: `v := 4c/3` (`c` from `hMGL`), `V` from `hV : NormalizedVolumeBounded_S13 Hp`; `X` = the stage at a
  common late regular time `t*` (so `hV` applies), `μ` = normalised Riemannian volume, `A i := map_i t* '' B(x_i, 2)`;
  disjointness is the `DISJ` hypothesis, `μ (A i) ≥ (2/3) c = v/2`, `μ univ ≤ V`.
  The Margulis input `hMGL` is the frozen shape of sheet S2 (`scratch/SheetH3H5_O15.lean`). -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set MeasureTheory Filter
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness Function
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

theorem vol_univ_transport_S100 {Q Q' : OrientedThreeStage.{u}} (e : Q = Q') {m : Q.Metric}
    {m' : Q'.Metric} (hm : HEq m m') (c : ℝ) (hc : 0 < c) :
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) Q.Carrier
      (scaleMetric c hc m) univ =
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) Q'.Carrier
      (scaleMetric c hc m') univ := by
  subst e
  rw [eq_of_heq hm]

theorem post_vol_univ_eq_S100 {P : OrientedThreeStage.{u}} {g : P.Metric} (O : ObservationTower P g)
    (s : RegularSlice O) :
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) (postStage O s.time).Carrier
      (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive) (postMetric O s.time)) univ =
    normalizedTotalVolume_S13 s :=
  vol_univ_transport_S100 (postStage_regularSlice O s) (postMetric_regularSlice O s) _ _

/-- One model datum: the image of `B(x, 2)` at a late time `t` (open, inside the slice image, volume `≥ 2/3`). -/
theorem core_image_S100 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (H : FiniteVolumeHyperbolicModel.{u}) (start : ℝ) (hstart : 0 < start) (α : ℝ → ℝ)
    (Ω : TopologicalSpace.Opens (ℝ × H.Carrier))
    (map : (t : ℝ) → start ≤ t → H.Carrier → (postStage F.observation t).Carrier)
    (hpos : ∀ t, start ≤ t → 0 < α t) (hdecay : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε)
    (hemb : ∀ t (ht : start ≤ t),
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => map t ht x))
    (hsmooth : ∀ t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map t ht) (sourceSlice_CX5 Ω t))
    (hball : ∀ t, start ≤ t →
      riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t)
    (hck : ∀ t (ht : start ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹),
        ckErr_O21 H (postMetric F.observation t) t⁻¹ (map t ht) k p < α t)
    (t : ℝ) (ht : start ≤ t) (hδ : α t ≤ 1 / 8) (x : H.Carrier) (D : ℝ) (hD0 : 0 ≤ D)
    (hxD : x ∈ riemannianBallOf H.metric H.basepoint D) (hD2 : D + 2 ≤ (α t)⁻¹) :
    IsOpen (map t ht '' riemannianBallOf H.metric x 2) ∧
    map t ht '' riemannianBallOf H.metric x 2 ⊆ map t ht '' (sourceSlice_CX5 Ω t : Set H.Carrier) ∧
    ENNReal.ofReal (2 / 3) * ballVolume H.metric x 2 ≤
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3)
        (postStage F.observation t).Carrier
        (scaleMetric t⁻¹ (inv_pos.mpr (hstart.trans_le ht)) (postMetric F.observation t))
        (map t ht '' riemannianBallOf H.metric x 2) := by
  have hD : ((∀ t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : start ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => map t ht x)) ∧
      (∀ t, start ≤ t → riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : start ≤ t),
        let h := H.metric; let error := fun p : H.Carrier =>
          ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
            ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (map t ht) p - h.inner p)).uncurryLeft;
        ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf h H.basepoint (2 * (α t)⁻¹),
            tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < α t) ∧
      (∀ t, start ≤ t → 0 < α t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε)) :=
    ⟨hsmooth, hemb, hball, fun t ht => by intro h error k hk p hp; exact hck t ht k hk p hp,
      hpos, hdecay⟩
  have hαpos := hpos t ht
  have hy : x ∈ riemannianBallOf H.metric H.basepoint (α t)⁻¹ :=
    riemannianBallOf_mono _ _ (by linarith) hxD
  have hRn : (2 : ℝ) ≤ (α t)⁻¹ := by linarith
  have hS : IsOpen (riemannianBallOf H.metric x 2) := isOpen_riemannianBallOf _ _ _
  have hSR : riemannianBallOf H.metric x 2 ⊆ riemannianClosedBallOf H.metric x 2 :=
    fun z hz => by
      change riemannianEDistOf H.metric x z ≤ ENNReal.ofReal 2
      exact (show riemannianEDistOf H.metric x z < ENNReal.ofReal 2 from hz).le
  have hsub := closedBall_subset_buffer_O27 hD t ht x hy hRn
  have hAU : riemannianBallOf H.metric x 2 ⊆ (sourceSlice_CX5 Ω t : Set H.Carrier) :=
    fun z hz => hball t ht (hsub (hSR hz))
  have himg : (fun z : sourceSlice_CX5 Ω t => map t ht z) ''
      ((Subtype.val : sourceSlice_CX5 Ω t → H.Carrier) ⁻¹' riemannianBallOf H.metric x 2) =
      map t ht '' riemannianBallOf H.metric x 2 := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.val, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hAU hw⟩, hw, rfl⟩
  refine ⟨?_, Set.image_mono hAU, ?_⟩
  · obtain ⟨hf, -⟩ := bufferedMap_localDiffeo_O27 hD t ht
    rw [← himg]
    exact hf.isOpenMap _ (hS.preimage continuous_subtype_val)
  · exact image_volume_lower_S100 hstart hD t ht x hy hRn hδ hS hSR

/-- **G2.**  `hvolw` of `exists_disjoint_family_of_steps_O41`, from `hV` and the Margulis input `hMGL`. -/
theorem hvolw_S100 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hV : NormalizedVolumeBounded_S13 Hp)
    (hMGL : ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ H : FiniteVolumeHyperbolicModel.{u}, ∃ x : H.Carrier,
      ∀ y ∈ riemannianBallOf H.metric x a, ENNReal.ofReal c ≤ ballVolume H.metric y 2) :
    ∃ v V : ℝ, 0 < v ∧ 0 ≤ V ∧
      ∀ (count : ℕ) (model : Fin count → FiniteVolumeHyperbolicModel.{u})
        (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
        (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
        (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier),
        (      (∀ i, 0 < start i) ∧
      (∀ i t, start i ≤ t → 0 < α i t) ∧ (∀ i, AntitoneOn (α i) (Ici (start i))) ∧
      (∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε) ∧
      (∀ i t (ht : start i ≤ t),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t)) ∧
      (∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x)) ∧
      (∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
        (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t) ∧
      (∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t) ∧
      (∀ i t (_ht : start i ≤ t), ∀ x ∈ sourceSlice_CX5 (Ω i) t,
        Nonempty (PersistentModelPatch F (model i) (start i) (α i)
          (sourceSlice_CX5 (Ω i)) (map i) t x))) →       (∃ Td : ℝ, ∀ t (i j : Fin count) (hi : start i ≤ t) (hj : start j ≤ t), Td ≤ t → i ≠ j →
        Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
          (map j t hj '' (sourceSlice_CX5 (Ω j) t : Set (model j).Carrier))) →
        ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (A : Fin count → Set X),
          (∀ i, MeasurableSet (A i)) ∧ Pairwise (Disjoint on A) ∧
          (∀ i, ENNReal.ofReal (v / 2) ≤ μ (A i)) ∧ μ univ ≤ ENNReal.ofReal V := by
  classical
  obtain ⟨a, c, ha, hc, hmgl⟩ := hMGL
  obtain ⟨V₀, hV0, hVs⟩ := hV
  refine ⟨4 * c / 3, V₀, by positivity, hV0.le, ?_⟩
  intro count model start α Ω map h9 hdisj
  obtain ⟨hst, hpos, -, hdecay, hsmooth, hemb, hball, hck, -⟩ := h9
  obtain ⟨Td, hTd⟩ := hdisj
  choose x hx using fun i => hmgl (model i)
  let D : Fin count → ℝ := fun i =>
    (riemannianEDistOf (model i).metric (model i).basepoint (x i)).toReal + 1
  have hD0 : ∀ i, 0 ≤ D i := fun i => by
    have := ENNReal.toReal_nonneg (a := riemannianEDistOf (model i).metric (model i).basepoint (x i))
    simp only [D]; linarith
  have hxD : ∀ i, x i ∈ riemannianBallOf (model i).metric (model i).basepoint (D i) := fun i => by
    have hne := riemannianEDistOf_ne_top (I := 𝓡 3) (model i).metric (model i).basepoint (x i)
    change riemannianEDistOf (model i).metric (model i).basepoint (x i) < ENNReal.ofReal (D i)
    simp only [D]
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hne,
      ENNReal.ofReal_one]
    exact ENNReal.lt_add_right hne one_ne_zero
  choose Tα hTα using fun i => hdecay i (D i + 3)⁻¹
    (inv_pos.mpr (by linarith [hD0 i]))
  choose Tα' hTα' using fun i => hdecay i (1 / 8) (by norm_num)
  let T₀ : ℝ := max (max Td 1) (∑ i, (|start i| + |Tα i| + |Tα' i|))
  obtain ⟨s, hs⟩ := exists_regularSlice_mem_Ioo_O7 F.observation
    (by have := le_max_right Td 1; have := le_max_left (max Td 1) (∑ i, (|start i| + |Tα i| + |Tα' i|))
        linarith) (lt_add_one T₀)
  have hsT : T₀ ≤ s.time := hs.1.le
  have hTi : ∀ i, |start i| + |Tα i| + |Tα' i| ≤ s.time := fun i =>
    (Finset.single_le_sum (f := fun i => |start i| + |Tα i| + |Tα' i|) (fun j _ => by positivity)
      (Finset.mem_univ i)).trans ((le_max_right _ _).trans hsT)
  have hi' : ∀ i, start i ≤ s.time := fun i =>
    (le_abs_self _).trans (by linarith [abs_nonneg (Tα i), abs_nonneg (Tα' i), hTi i])
  have hα1 : ∀ i, α i s.time < (D i + 3)⁻¹ := fun i =>
    hTα i _ ((le_abs_self _).trans (by linarith [abs_nonneg (start i), abs_nonneg (Tα' i), hTi i]))
  have hα8 : ∀ i, α i s.time ≤ 1 / 8 := fun i =>
    (hTα' i _ ((le_abs_self _).trans
      (by linarith [abs_nonneg (start i), abs_nonneg (Tα i), hTi i]))).le
  have hD2 : ∀ i, D i + 2 ≤ (α i s.time)⁻¹ := fun i => by
    have h := (lt_inv_comm₀ (hpos i _ (hi' i)) (by linarith [hD0 i])).mp (hα1 i)
    linarith
  have hTdle : Td ≤ s.time := (le_max_left Td 1).trans ((le_max_left _ _).trans hsT)
  have h1le : 1 ≤ s.time := (le_max_right Td 1).trans ((le_max_left _ _).trans hsT)
  have core := fun i => core_image_S100 F K (model i) (start i) (hst i) (α i) (Ω i) (map i)
    (hpos i) (hdecay i) (hemb i) (hsmooth i) (hball i) (hck i) s.time (hi' i) (hα8 i) (x i)
    (D i) (hD0 i) (hxD i) (hD2 i)
  let : MeasurableSpace (postStage F.observation s.time).Carrier := borel _
  have : BorelSpace (postStage F.observation s.time).Carrier := ⟨rfl⟩
  refine ⟨(postStage F.observation s.time).Carrier, inferInstance,
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3)
      (postStage F.observation s.time).Carrier
      (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive) (postMetric F.observation s.time)),
    fun i => map i s.time (hi' i) '' riemannianBallOf (model i).metric (x i) 2, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (core i).1.measurableSet
  · intro i j hij
    exact Disjoint.mono (core i).2.1 (core j).2.1 (hTd s.time i j (hi' i) (hi' j) hTdle hij)
  · intro i
    have hself : x i ∈ riemannianBallOf (model i).metric (x i) a := by
      change riemannianEDistOf (model i).metric (x i) (x i) < ENNReal.ofReal a
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr ha
    have h1 := hx i (x i) hself
    have h2 : ENNReal.ofReal (4 * c / 3 / 2) = ENNReal.ofReal (2 / 3) * ENNReal.ofReal c := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    rw [h2]
    exact (mul_le_mul' le_rfl h1).trans (core i).2.2
  · rw [post_vol_univ_eq_S100 F.observation s]
    exact hVs s h1le

end GC.LongTime.Ch12
