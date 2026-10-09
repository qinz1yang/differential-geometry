import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreSpec
import DifferentialGeometry.Geometry.Collapse.Inhabitants.SmallBoundaryPackets

/-!
# BCG06 consumers: the original map and the double cusp `T² × [0, 240]` (lane BCG6-K)

Concrete consumers of the BCG06 kernel (groups G1–G4a), review 65 M4 instance precision: the
kernel is applied to the ORIGINAL boundary pairs `(u_b, v_b) = F_{∂,b} = P.block b` (the map
`E = F_∂`, zero actual error) with POSITIVE tolerances `ε∂ = 10⁻⁷`, `c₃ = 10⁻⁶`.

* `original_BI_BCG6K`, `original_BFM_BCG6K`, `original_BD_BCG6K`: the three premises for `E = F_∂`;
  `chainBoundary_original_eq_BCG6K`: BCG7-COLLAR's `J_b ∘ F_∂` is the same pair, so the front of
  `J_b ∘ F_∂` is the front of `P.block b`;
* `original_cuspCore_labelled_product_BCG6K`, `original_frontier_cuspCore_BCG6K`: for every
  collar packet with `ε ≤ 1/1000` and every component, the core of the original map is a labelled
  `T² × [0, 1]` with relative frontier the front;
* regression (review 65 M4): `exists_band_root_not_front_BCG6K` — there is a band point with
  `u_b = 40` (the second root of `η ζ(η) = 40`, `η > 78`) that is NOT in the front: `H_b` is never
  `{u = 40} ∩ band`;
* `doubleCusp_boundaryGeometricOutput_BCG6K`: on the double cusp `T² × [0, 240]` (two ends, the
  export packet of `exists_doubleCuspBoundaryExport`) both ends carry the labelled core and the
  geometric output exists (the instance takes the product branch).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Topology.Manifold
open GC.Seifert

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

namespace BoundaryCollarPacket

variable (P : BoundaryCollarPacket W g K A w₀ ε)

/-- The first boundary coordinate of the original map, `u_b = (P.block b).1`. -/
def originalBoundaryU_BCG6K (b : Fin P.cusp.count) (x : W.Carrier) : ℝ := (P.block b x).1

/-- The marker of the original map, `v_b = (P.block b).2`. -/
def originalBoundaryV_BCG6K (b : Fin P.cusp.count) (x : W.Carrier) : ℝ := (P.block b x).2

theorem contMDiff_originalBoundaryU_BCG6K (b : Fin P.cusp.count) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (P.originalBoundaryU_BCG6K b) :=
  contDiff_fst.contMDiff.comp (P.contMDiff_block b)

/-- (BI) for `E = F_∂` at any positive tolerance. -/
theorem original_BI_BCG6K {εd : ℝ} (hεd : 0 < εd) (b : Fin P.cusp.count) (x : W.Carrier) :
    |P.originalBoundaryU_BCG6K b x - (P.block b x).1| < εd ∧
      |P.originalBoundaryV_BCG6K b x - (P.block b x).2| < εd := by
  simp only [originalBoundaryU_BCG6K, originalBoundaryV_BCG6K, sub_self, abs_zero]
  exact ⟨hεd, hεd⟩

/-- (BFM) for `E = F_∂`: the marker is `1` on `Safe_b`. -/
theorem original_BFM_BCG6K (b : Fin P.cusp.count) :
    ∀ x ∈ P.safeBand_BAUGA b, P.originalBoundaryV_BCG6K b x = 1 :=
  fun _ hx => P.cutoff_eq_one_of_mem_safeBand_BAUGA b hx

/-- (BD) for `E = F_∂`: near a band point with `38 ≤ η_b ≤ 42`, `u_b = η_b`. -/
theorem original_BD_BCG6K {c₃ : ℝ} (hc₃ : 0 ≤ c₃) (b : Fin P.cusp.count) :
    ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x,
        |mvfderiv W.model (fun y => P.originalBoundaryU_BCG6K b y - P.height b y) x w| ≤
          c₃ * Real.sqrt (g.inner x w w) := by
  intro x hx h38 h42 w
  have hO : IsOpen (P.collarBand_BAUGA b ∩ {y | 32 < P.height b y ∧ P.height b y < 78}) :=
    (P.isOpen_collarBand_BAUGA b).inter ((isOpen_lt continuous_const
      (P.contMDiff_height b).continuous).inter (isOpen_lt (P.contMDiff_height b).continuous
        continuous_const))
  have heq : (fun y => P.originalBoundaryU_BCG6K b y - P.height b y) =ᶠ[𝓝 x]
      fun _ => (0 : ℝ) := by
    filter_upwards [hO.mem_nhds ⟨hx, by linarith, by linarith⟩] with y hy
    rw [originalBoundaryU_BCG6K, P.block_eq_of_mem_safeBand_BAUGA b ⟨hy.1, hy.2.1.le, hy.2.2.le⟩,
      sub_self]
  rw [mvfderiv_congr_BCG6K heq, mvfderiv_const]
  simp only [zero_apply, abs_zero]
  exact mul_nonneg hc₃ (Real.sqrt_nonneg _)

/-- BCG7-COLLAR's `J_b ∘ F_∂` is the original pair. -/
theorem chainBoundary_original_eq_BCG6K {ι : Type*}
    (Fint : W.Carrier → BlockSpace (fun _ : ι => ℝ²)) :
    chainBoundaryU_BCG6K (boundaryOriginalMap_BAUGA P Fint) = P.originalBoundaryU_BCG6K ∧
      chainBoundaryV_BCG6K (boundaryOriginalMap_BAUGA P Fint) = P.originalBoundaryV_BCG6K := by
  constructor <;> funext b x <;>
    simp only [chainBoundaryU_BCG6K, chainBoundaryV_BCG6K, originalBoundaryU_BCG6K,
      originalBoundaryV_BCG6K, boundaryOriginalMap_BAUGA,
      augmentedBoundaryCoord_boundaryAugmentedMap_BC7C]

/-- **Consumer: the labelled core of the original map** for every collar packet with
`ε ≤ 1/1000` and every component. -/
theorem original_cuspCore_labelled_product_BCG6K (hε : ε ≤ 1 / 1000) (b : Fin P.cusp.count) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3)
        (P.cuspCore_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K),
      letI := cs
      IsManifold (𝓡∂ 3) ∞
          (P.cuspCore_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K) ∧
      ContMDiff (𝓡∂ 3) W.model ∞
        (fun y : P.cuspCore_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K =>
          (y : W.Carrier)) ∧
      (∀ y : P.cuspCore_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K,
        (𝓡∂ 3).IsBoundaryPoint y ↔ ((y : W.Carrier) ∈ P.cusp.component b ∨
          (y : W.Carrier) ∈
            P.cuspFront_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K)) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1)
          (P.cuspCore_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K) ∞,
        (∀ p, (D p : W.Carrier) ∈ P.cusp.component b ↔ (p.2 : ℝ) = 0) ∧
        ∀ p, (D p : W.Carrier) ∈
            P.cuspFront_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K ↔
          (p.2 : ℝ) = 1 :=
  P.cuspCore_labelled_product_BCG6K hε (P.contMDiff_originalBoundaryU_BCG6K b)
    (εd := 1 / 10000000) (c₃ := 1 / 1000000) (by norm_num) (by norm_num) (by norm_num)
    (P.original_BI_BCG6K (by norm_num) b) (P.original_BFM_BCG6K b)
    (P.original_BD_BCG6K (by norm_num) b)

/-- **Consumer: the relative frontier of the original core** is the original front. -/
theorem original_frontier_cuspCore_BCG6K (hε : ε ≤ 1 / 1000) (b : Fin P.cusp.count) :
    frontier (P.cuspCore_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K) =
      P.cuspFront_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K :=
  P.frontier_cuspCore_BCG6K hε (P.contMDiff_originalBoundaryU_BCG6K b)
    (εd := 1 / 10000000) (c₃ := 1 / 1000000) (by norm_num) (by norm_num) (by norm_num)
    (P.original_BI_BCG6K (by norm_num) b) (P.original_BFM_BCG6K b)
    (P.original_BD_BCG6K (by norm_num) b)

/-- **Regression (review 65 M4)**: the original map has a band point with `u_b = 40` that is
not in the front (the second root of `η ζ(η) = 40`, between heights `79` and `91`), so the front
is never `{u = 40} ∩ band`. -/
theorem exists_band_root_not_front_BCG6K (b : Fin P.cusp.count) :
    ∃ x ∈ P.collarBand_BAUGA b, P.originalBoundaryU_BCG6K b x = 40 ∧
      x ∉ P.cuspFront_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K := by
  obtain ⟨θ₀⟩ := (inferInstance : Nonempty Torus)
  have hε1 := P.tolerance_le_one
  have hz : ∀ s : ℝ, 0 ≤ s → ((θ₀, halfSpaceOneLift s) : CuspHalfSpace).2.val 0 = s := by
    intro s hs
    change (halfSpaceOneLift s).1 0 = s
    rw [halfSpaceOneLift_val_zero, max_eq_left hs]
  have hband : ∀ s : ℝ, 3 ≤ s → s ≤ 97 →
      (P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s) ∈ P.collarBand_BAUGA b ∧
        |P.height b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s)) - s| < 1 := by
    intro s h3 h97
    have hzs := hz s (by linarith)
    have hd : ((θ₀, halfSpaceOneLift s) : CuspHalfSpace) ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 97) (by norm_num [cuspDepth]) (by rw [hzs]; exact h97)
    have hc := (P.height_contract b _ hd (by rw [hzs]; linarith) (by rw [hzs]; linarith)).1
    rw [hzs] at hc
    exact ⟨⟨_, ⟨by rw [hzs]; linarith, by rw [hzs]; linarith⟩, rfl⟩, hc.trans_le hε1⟩
  obtain ⟨hb79, hc79⟩ := hband 79 (by norm_num) (by norm_num)
  obtain ⟨hb92, hc92⟩ := hband 92 (by norm_num) (by norm_num)
  have h79 := abs_lt.mp hc79
  have h92 := abs_lt.mp hc92
  have hval : ∀ x ∈ P.collarBand_BAUGA b,
      P.originalBoundaryU_BCG6K b x = P.height b x * boundaryProfile (P.height b x) := by
    intro x hx
    rw [originalBoundaryU_BCG6K, P.block_eq_of_mem_collarBand_BAUGA b hx, boundaryBlock_fst]
  have hu79 : P.originalBoundaryU_BCG6K b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift 79)) =
      P.height b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift 79)) := by
    rw [hval _ hb79, boundaryProfile_eq_one ⟨by linarith, by linarith⟩, mul_one]
  have hu92 : P.originalBoundaryU_BCG6K b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift 92)) =
      0 := by
    rw [hval _ hb92, boundaryProfile_eq_zero_of_ge (by linarith), mul_zero]
  have hc1 : ContinuousOn (fun s : ℝ => ((θ₀, halfSpaceOneLift s) : CuspHalfSpace))
      (Icc 79 92) :=
    contMDiffOn_cuspVertical.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      fun s hs => ⟨mem_univ _, show (0 : ℝ) ≤ s by linarith [hs.1]⟩
  have hc2 : ContinuousOn (fun s : ℝ => (P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s))
      (Icc 79 92) :=
    (P.cusp.collar b).contMDiffOn.continuousOn.comp hc1 fun s hs => by
      change ((θ₀, halfSpaceOneLift s) : CuspHalfSpace).2.val 0 < cuspDepth
      rw [hz s (by linarith [hs.1]), cuspDepth]
      linarith [hs.2]
  have hc3 : ContinuousOn (fun s : ℝ =>
      P.originalBoundaryU_BCG6K b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s)))
      (Icc 79 92) :=
    (P.contMDiff_originalBoundaryU_BCG6K b).continuous.comp_continuousOn hc2
  have h40 : (40 : ℝ) ∈ Icc
      (P.originalBoundaryU_BCG6K b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift 92)))
      (P.originalBoundaryU_BCG6K b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift 79))) :=
    ⟨by rw [hu92]; norm_num, by rw [hu79]; linarith⟩
  obtain ⟨s, hs, hs40⟩ := intermediate_value_Icc' (by norm_num : (79 : ℝ) ≤ 92) hc3 h40
  obtain ⟨hbs, hcs⟩ := hband s (by linarith [hs.1]) (by linarith [hs.2])
  refine ⟨_, hbs, hs40, fun hH => ?_⟩
  obtain ⟨-, hloc⟩ := P.front_height_BCG6K b (εd := 1 / 10000000) (by norm_num)
    (P.original_BI_BCG6K (by norm_num) b _).1 (P.original_BI_BCG6K (by norm_num) b _).2 hH
  have h1 := abs_lt.mp hloc
  have h2 := abs_lt.mp hcs
  linarith [hs.1]

end BoundaryCollarPacket

/-- The double cusp carrier is connected (as in `SmallBoundaryPackets`). -/
local instance connectedSpace_annulusCircleCarrier_BCG6K :
    ConnectedSpace annulusCircleCarrier.{u}.Carrier :=
  connectedSpace_productSet (Or.inl rfl)

/-- **Consumer on the double cusp `T² × [0, 240]`**: the export packet of the two-ended double
cusp (`w₀ = 1/6408`, tolerance `1/1000`) carries, for both ends, the labelled core of the original
map, and the BCG06 geometric output exists (no zero balls are involved; the instance takes the
product branch of the packet's alternative). -/
theorem doubleCusp_boundaryGeometricOutput_BCG6K (K : ℕ) (hK : 2 ≤ K) :
    ∃ a : ℝ, ∃ ha : 0 < a, ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧
      ∃ P : BoundaryExportPacket annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) K A
          (1 / 6408) (1 / 1000),
        P.cusp.count = 2 ∧
        (∀ b, frontier (P.cuspCore_BCG6K b P.originalBoundaryU_BCG6K
            P.originalBoundaryV_BCG6K) =
          P.cuspFront_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K) ∧
        BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K P.toBoundaryCollarPacket
          P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K (Empty.elim : Empty → Set _) := by
  obtain ⟨a, ha, A, hA, P, hc⟩ := exists_doubleCuspBoundaryExport.{u} K hK (1 / 6408) (1 / 1000)
    (by norm_num) le_rfl (by norm_num) le_rfl
  refine ⟨a, ha, A, hA, P, hc, fun b => P.original_frontier_cuspCore_BCG6K le_rfl b, ?_⟩
  refine P.boundaryGeometricOutput_BCG6K le_rfl (fun b => P.contMDiff_originalBoundaryU_BCG6K b)
    (εd := 1 / 10000000) (c₃ := 1 / 1000000) (by norm_num) (by norm_num) (by norm_num)
    (fun b => P.original_BI_BCG6K (by norm_num) b) (fun b => P.original_BFM_BCG6K b)
    (fun b => P.original_BD_BCG6K (by norm_num) b) _ ?_
  rcases P.alternative with hprod | hsep
  · exact Or.inl hprod
  · exact Or.inr ⟨fun i j hij => (hsep i j hij).1, fun j => j.elim⟩

end DifferentialGeometry.Geometry.Collapse
