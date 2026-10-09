import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickRadiusTransfer_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61
import DifferentialGeometry.Topology.Manifold.ImmersionRange
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

set_option autoImplicit false

/-! # CH12-O44 G1: fixed-radius DISJ of a new model against an old family ([FROZEN] CH12-O44).

* `exists_frontier_preimage_O44`: a preconnected set meeting the open image `f '' B` and its complement
  meets `f '' (C \ B)` when `B ⊆ C`, `C` compact and `f` continuous on `C`.
* `isOpen_image_slice_O44`: the image of an open subset of the slice under the smooth embedding is open.
* `disjoint_fixed_radius_O44`: for an old family with INV2 (hpi07 inputs at `β_i` on a larger `Ω'_i`
  and `slice ⊆ B(1/(2β_i))`) there is `R0` such that every new model whose basepoint image is
  `wstar`-thick and escapes the old images of `B(R0 i)` has, for each fixed radius `R` at which the
  HLOW thickness bound holds, the image of `B_H(R)` eventually disjoint from all old full slices.
  Proof: basepoint escape (hpi07 contrapositive, R0 i = 1/min(wstar, w0_i) + 1), frontier of
  `map_i '' B(1/(2β_i))`, thick transfer at the frontier point (depth `1/(2β_i t) → ∞`). -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

theorem exists_frontier_preimage_O44 {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
    [T2Space X] (f : M → X) {B C : Set M} (hBC : B ⊆ C) (hC : IsCompact C)
    (hfC : ContinuousOn f C) (hA : IsOpen (f '' B)) {N : Set X} (hN : IsPreconnected N)
    {x0 : X} (hx0 : x0 ∈ N) (hx0A : x0 ∉ f '' B) (hNA : (N ∩ f '' B).Nonempty) :
    ∃ q ∈ C, q ∉ B ∧ f q ∈ N := by
  by_contra hcon
  push Not at hcon
  have hcl : IsClosed (f '' C) := (hC.image_of_continuousOn hfC).isClosed
  have hsub : N ⊆ f '' B ∪ (f '' C)ᶜ := by
    intro p hp
    by_cases hpc : p ∈ f '' C
    · obtain ⟨q, hq, rfl⟩ := hpc
      by_cases hqB : q ∈ B
      · exact Or.inl ⟨q, hqB, rfl⟩
      · exact absurd hp (hcon q hq hqB)
    · exact Or.inr hpc
  have hx0v : x0 ∈ (f '' C)ᶜ := (hsub hx0).resolve_left hx0A
  obtain ⟨p, -, hpA, hpv⟩ := hN _ _ hA hcl.isOpen_compl hsub hNA ⟨x0, hx0, hx0v⟩
  obtain ⟨q, hq, rfl⟩ := hpA
  exact hpv ⟨q, hBC hq, rfl⟩

theorem isOpen_image_slice_O44 {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ X] (U : TopologicalSpace.Opens M) (f : M → X)
    (hf : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x)) {B : Set M} (hB : IsOpen B)
    (hBU : B ⊆ U) : IsOpen (f '' B) := by
  have hrange : IsOpen (Set.range (fun x : U => f x)) :=
    Manifold.isOpen_range_of_isSmoothEmbedding (I := 𝓡 3) (J := 𝓡 3) rfl hf
  have hOE : Topology.IsOpenEmbedding (fun x : U => f x) := ⟨hf.isEmbedding, hrange⟩
  have himg : f '' B = (fun x : U => f x) '' (Subtype.val ⁻¹' B) := by
    ext z; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hBU hx⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [himg]
  exact hOE.isOpenMap _ (hB.preimage continuous_subtype_val)

theorem riemannianClosedBallOf_subset_ballOf_O44 (H : FiniteVolumeHyperbolicModel.{u})
    {r r' : ℝ} (hr : 0 ≤ r) (h : r < r') :
    riemannianClosedBallOf H.metric H.basepoint r ⊆ riemannianBallOf H.metric H.basepoint r' :=
  fun _ hx => lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (hr.trans_lt h)).mpr h)

theorem disjoint_fixed_radius_O44 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hHG03 : ∀ H : FiniteVolumeHyperbolicModel.{u}, Nonempty (HyperbolicTruncation H))
    (wstar : ℝ) (hw : 0 < wstar) {count : ℕ} (model : Fin count → FiniteVolumeHyperbolicModel.{u})
    (start : Fin count → ℝ) (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
    (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier)
    (hstart : ∀ i, 0 < start i)
    (hinv2 : ∀ i, ∃ (β : ℝ → ℝ) (Ω' : TopologicalSpace.Opens (ℝ × (model i).Carrier)),
      (∀ t, start i ≤ t → 0 < β t) ∧ (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → β t < ε) ∧
      (∀ t (ht : start i ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 Ω' t)) ∧
      (∀ t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : sourceSlice_CX5 Ω' t => map i t ht x)) ∧
      (∀ t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint (2 * (β t)⁻¹) ⊆
        sourceSlice_CX5 Ω' t) ∧
      (∀ t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(β t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (β t)⁻¹),
          ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < β t) ∧
      (∀ t, start i ≤ t → (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier) ⊆
        riemannianBallOf (model i).metric (model i).basepoint (2 * β t)⁻¹)) :
    ∃ R0 : Fin count → ℝ, ∀ (H : FiniteVolumeHyperbolicModel.{u}) (sH : ℝ) (hsH : 0 < sH)
      (αH : ℝ → ℝ) (ΩH : TopologicalSpace.Opens (ℝ × H.Carrier))
      (mapH : (t : ℝ) → sH ≤ t → H.Carrier → (postStage F.observation t).Carrier),
      (∀ t, sH ≤ t → 0 < αH t) → (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → αH t < ε) →
      (∀ t (ht : sH ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mapH t ht) (sourceSlice_CX5 ΩH t)) →
      (∀ t, sH ≤ t → riemannianBallOf H.metric H.basepoint (2 * (αH t)⁻¹) ⊆ sourceSlice_CX5 ΩH t) →
      (∀ t (ht : sH ≤ t), ∀ y ∈ riemannianBallOf H.metric H.basepoint 1, ∃ r : ℝ, 0 < r ∧
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hsH.trans_le ht))
          (postMetric F.observation t)) (mapH t ht y) = ENNReal.ofReal r ∧
        ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
          (inv_pos.mpr (hsH.trans_le ht)) (postMetric F.observation t)) (mapH t ht y) r) →
      (∀ i : Fin count, ∃ T : ℝ, ∀ t (hn : sH ≤ t) (hi : start i ≤ t), T ≤ t →
        mapH t hn H.basepoint ∉
          map i t hi '' riemannianBallOf (model i).metric (model i).basepoint (R0 i)) →
      ∀ R : ℝ, (∃ w : ℝ, 0 < w ∧ ∃ T : ℝ, ∀ t (ht : sH ≤ t), T ≤ t →
        ∀ y ∈ riemannianBallOf H.metric H.basepoint R, ∃ r : ℝ, 0 < r ∧
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (hsH.trans_le ht))
            (postMetric F.observation t)) (mapH t ht y) = ENNReal.ofReal r ∧
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹
            (inv_pos.mpr (hsH.trans_le ht)) (postMetric F.observation t)) (mapH t ht y) r) →
      ∃ T : ℝ, ∀ t (i : Fin count) (hi : start i ≤ t) (hn : sH ≤ t), T ≤ t →
        Disjoint (map i t hi '' (sourceSlice_CX5 (Ω i) t : Set (model i).Carrier))
          (mapH t hn '' riemannianBallOf H.metric H.basepoint R) := by
  choose β Ω' hβpos hβdec hsm hem hba hck hinv using hinv2
  have key := fun i => hpi07_thick_transfer_O27 F K (model i) (Classical.choice (hHG03 (model i)))
    (start i) (hstart i) (β i) (Ω' i) (map i) (hβpos i) (hβdec i) (hem i) (hsm i) (hba i) (hck i)
  choose w0 hw0 T7 hT7 using key
  refine ⟨fun i => (min wstar (w0 i))⁻¹ + 1, ?_⟩
  intro H sH hsH αH ΩH mapH hαpos hαdec hHsm hHba hthick hesc R hlow
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨0, fun t i hi hn _ => Set.disjoint_left.mpr fun z _ hz => ?_⟩
    obtain ⟨y, hy, -⟩ := hz
    have hy' : riemannianEDistOf H.metric H.basepoint y < ENNReal.ofReal R := hy
    rw [ENNReal.ofReal_of_nonpos hR] at hy'
    exact ENNReal.not_lt_zero hy'
  obtain ⟨w, hwpos, TL, hTL⟩ := hlow
  have hv : ∀ i, 0 < min w (w0 i) := fun i => lt_min hwpos (hw0 i)
  choose Tb hTb using fun i => hβdec i (min w (w0 i) / 2) (half_pos (hv i))
  choose Te hTe using hesc
  obtain ⟨Tα, hTα⟩ := hαdec (2 / R) (div_pos two_pos hR)
  refine ⟨max (max TL Tα) (∑ i, (|T7 i| + |Tb i| + |Te i|)), ?_⟩
  intro t i hi hn hT
  have hle : |T7 i| + |Tb i| + |Te i| ≤ t :=
    (Finset.single_le_sum (f := fun j => |T7 j| + |Tb j| + |Te j|) (fun j _ => by positivity)
      (Finset.mem_univ i)).trans ((le_max_right _ _).trans hT)
  have hT7i : T7 i ≤ t := (le_abs_self _).trans (by linarith [abs_nonneg (Tb i), abs_nonneg (Te i)])
  have hTbi : Tb i ≤ t := (le_abs_self _).trans (by linarith [abs_nonneg (T7 i), abs_nonneg (Te i)])
  have hTei : Te i ≤ t := (le_abs_self _).trans (by linarith [abs_nonneg (T7 i), abs_nonneg (Tb i)])
  have hTLt : TL ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hTαt : Tα ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  -- radii
  have hb := hβpos i t hi
  set ρ : ℝ := (2 * β i t)⁻¹ with hρ
  have hρpos : 0 < ρ := inv_pos.mpr (by positivity)
  have hρ1 : ρ < (β i t)⁻¹ := by
    rw [hρ, mul_inv]; nlinarith [inv_pos.mpr hb]
  have hρ2 : ρ < 2 * (β i t)⁻¹ := by nlinarith [inv_pos.mpr hb]
  have hCB : riemannianClosedBallOf (model i).metric (model i).basepoint ρ ⊆
      riemannianBallOf (model i).metric (model i).basepoint (β i t)⁻¹ :=
    riemannianClosedBallOf_subset_ballOf_O44 _ hρpos.le hρ1
  have hBC : riemannianBallOf (model i).metric (model i).basepoint ρ ⊆
      riemannianClosedBallOf (model i).metric (model i).basepoint ρ := fun x hx => by
    simp only [riemannianBallOf, riemannianClosedBallOf, Set.mem_ofPred_eq] at hx ⊢; exact hx.le
  have hCU : riemannianClosedBallOf (model i).metric (model i).basepoint ρ ⊆ sourceSlice_CX5 (Ω' i) t :=
    (riemannianClosedBallOf_subset_ballOf_O44 _ hρpos.le hρ2).trans (hba i t hi)
  have hAopen : IsOpen (map i t hi '' riemannianBallOf (model i).metric (model i).basepoint ρ) :=
    isOpen_image_slice_O44 _ (map i t hi) (hem i t hi) (isOpen_riemannianBallOf_S61 _ _)
      (hBC.trans hCU)
  -- thick transfer at level v ≤ w0 i
  have htr : ∀ (v : ℝ), 0 < v → v ≤ w0 i → ∀ q ∈ riemannianClosedBallOf (model i).metric
      (model i).basepoint ρ, ∀ r : ℝ, 0 < r →
      curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ((hstart i).trans_le hi))
        (postMetric F.observation t)) (map i t hi q) = ENNReal.ofReal r →
      ENNReal.ofReal (v * r ^ 3) ≤ ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ((hstart i).trans_le hi))
        (postMetric F.observation t)) (map i t hi q) r →
      q ∈ riemannianBallOf (model i).metric (model i).basepoint v⁻¹ :=
    fun v hv0 hvle q hq r hr hcr hvol => hT7 i t hi hT7i v hv0 hvle q (hCB hq) r hr hcr hvol
  -- new image: path connected, contains the basepoint image
  have hRα : R < 2 * (αH t)⁻¹ := by
    have h1 := hTα t hTαt
    have hαpos := hαpos t hn
    rw [lt_div_iff₀ hR] at h1
    rw [← div_eq_mul_inv, lt_div_iff₀ hαpos]; linarith
  have hBH : riemannianBallOf H.metric H.basepoint R ⊆ sourceSlice_CX5 ΩH t :=
    (riemannianBallOf_mono _ _ hRα.le).trans (hHba t hn)
  have hNconn : IsPreconnected (mapH t hn '' riemannianBallOf H.metric H.basepoint R) :=
    ((isPathConnected_riemannianBallOf H.metric H.basepoint hR).image'
      ((hHsm t hn).continuousOn.mono hBH)).isConnected.isPreconnected
  have hbase : H.basepoint ∈ riemannianBallOf H.metric H.basepoint R := by
    change riemannianEDistOf H.metric H.basepoint H.basepoint < ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hR
  -- basepoint escape
  have hx0 : mapH t hn H.basepoint ∉ map i t hi '' riemannianBallOf (model i).metric
      (model i).basepoint ρ := by
    rintro ⟨q, hq, hqe⟩
    apply hTe i t hn hi hTei
    refine ⟨q, ?_, hqe⟩
    have hb1 : H.basepoint ∈ riemannianBallOf H.metric H.basepoint 1 := by
      change riemannianEDistOf H.metric H.basepoint H.basepoint < ENNReal.ofReal 1
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr one_pos
    obtain ⟨r, hr, hcr, hvol⟩ := hthick t hn H.basepoint hb1
    rw [← hqe] at hcr hvol
    have hv0 : 0 < min wstar (w0 i) := lt_min hw (hw0 i)
    have hmem := htr (min wstar (w0 i)) hv0 (min_le_right _ _) q (hBC hq) r hr hcr
      ((ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (by positivity : (0 : ℝ) ≤ r ^ 3))).trans hvol)
    exact riemannianBallOf_mono _ _ (by linarith) hmem
  -- frontier argument
  refine Set.disjoint_left.mpr fun z hz hzN => ?_
  obtain ⟨x, hx, rfl⟩ := hz
  have hzA : map i t hi x ∈ map i t hi '' riemannianBallOf (model i).metric (model i).basepoint ρ :=
    ⟨x, hinv i t hi hx, rfl⟩
  obtain ⟨q, hqC, hqB, hqN⟩ := exists_frontier_preimage_O44 (map i t hi) hBC
    (isCompact_riemannianClosedBallOf (model i).complete _ _)
    ((hsm i t hi).continuousOn.mono hCU) hAopen hNconn ⟨H.basepoint, hbase, rfl⟩ hx0
    ⟨_, hzN, hzA⟩
  obtain ⟨y, hy, hye⟩ := hqN
  obtain ⟨r, hr, hcr, hvol⟩ := hTL t hn hTLt y hy
  rw [hye] at hcr hvol
  have hmem := htr (min w (w0 i)) (hv i) (min_le_right _ _) q hqC r hr hcr
    ((ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (by positivity : (0 : ℝ) ≤ r ^ 3))).trans hvol)
  have hβv : 2 * β i t ≤ min w (w0 i) := by linarith [hTb i t hTbi]
  have hvρ : (min w (w0 i))⁻¹ ≤ ρ := by
    rw [hρ]; exact inv_anti₀ (by positivity) hβv
  exact hqB (riemannianBallOf_mono _ _ hvρ hmem)

end GC.LongTime.Ch12
