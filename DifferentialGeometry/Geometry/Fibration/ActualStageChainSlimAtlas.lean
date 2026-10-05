import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf0507Slim
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf07Stage
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimImage
import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasCoverBCF
import DifferentialGeometry.Topology.Manifold.SubmersionOpenMap

/-!
# ZSP04, closed side: the slim base as a graph atlas, the slab image in it, (SK), openness of `f₃`

Lane C14-ZSP35d. Blueprint `master207B.tex`, ZSP04 (B:6531–6595), first paragraph of the proof
(B:6564–6574); review 74 D74-9 (the shared `K₃` kernel is lane B-BCF134's; this file supplies its
CLOSED inputs on the chain, as agreed 14:5x): `f = π₃ ∘ E`, `R₃ = gaf07SlimRatio_G47` (GAF47's
FULL-norm ratio), `Bs = W₃ ∩ R₃`, atlas `coord j = R_j⁻¹ axis u_j`, `param j = ψ_j`
(`finalBase_slim_chart_BAS`), `dom j = B(0, 5.5·10⁵Δ) ∩ ψ_j⁻¹(R₃)`, `U = f⁻¹(Bs)`.

* `Gaf02ChainE.slimBs_ZSP35`, `slimParam_ZSP35`, `slimAtlas_ZSP35 : GraphAtlas1_BCF _ Bs` (the
  closed atlas; B-BCF134's `GraphAtlas1_BCF`).
* `Gaf02ChainE.slimSlabImage_subset_slimBs_ZSP35`: `f(⋃ slabs) ⊆ Bs` (threshold-5 patches of
  BASES + G2's ratio inclusion).
* `Gaf02ChainE.zsp04_SK_ZSP35` — (SK) up to `∂C₃`: for EVERY finite `F`, finitely many closed chart
  intervals with endpoints off `F` whose union `K'` is compact, lies in `Bs`, and contains the
  slab image in its relative interior (kernel (K-a), `exists_cover_union_BCF`).
* `Gaf02ChainEJA.slim_chart_local_ZSP35` (near every `p ∈ U`: `p ∈ Y_i`, `f = ψ_i ∘ g_i` on `Y_i`,
  `g_i` a submersion at `p`), `isOpen_slimSource_ZSP35` (`U` open),
  `slim_relOpen_ZSP35` (`f|U` is open onto `Bs`: images of open subsets of `U` are relatively open).

Consumer: `zsp04_SK_C14Z_ZSP35` (final family; chain with (JA) on its `C14` projection).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- ZSP04's base `Bs = W₃ ∩ R₃` (BASES' final slim base, GAF47's full-norm ratio set). -/
def slimBs_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  C.toChain.finalBase_BAS 2 ∩ gaf07SlimRatio_G47 P.toLocalChartPackets

/-- The chart `ψ_j` of `W₃` (`finalBase_slim_chart_BAS`, chosen). -/
def slimParam_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (j : P.slim.finite_centres.toFinset) :
    ℝ → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  Classical.choose (C.toChain.finalBase_slim_chart_BAS C.rough j)

theorem slimParam_spec_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset) :
    ContDiffOn ℝ ∞ (C.slimParam_ZSP35 j) (ball 0 (11 / 2 * (10 ^ 5 * Δ))) ∧
      (∀ b ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)),
        C.slimParam_ZSP35 j b ∈ C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∧
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (C.slimParam_ZSP35 j b) = b) ∧
      ∀ y ∈ C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ),
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) y ∈
            ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∧
          C.slimParam_ZSP35 j
            (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) y) =
            y :=
  Classical.choose_spec (C.toChain.finalBase_slim_chart_BAS C.rough j)

/-- **The closed slim base as a graph atlas** (B-BCF134's `GraphAtlas1_BCF`, the closed binding
agreed 14:5x): charts `ψ_j` on `B(0, 5.5·10⁵Δ) ∩ ψ_j⁻¹(R₃)` with linear left inverses
`R_j⁻¹ axis u_j`, pieces `Bs ∩ {marked j}`. -/
def slimAtlas_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    DifferentialGeometry.Topology.GraphAtlas1_BCF (P.slim.finite_centres.toFinset)
      C.slimBs_ZSP35 where
  coord j := (ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)
  param j := C.slimParam_ZSP35 j
  dom j := ball 0 (11 / 2 * (10 ^ 5 * Δ)) ∩
    C.slimParam_ZSP35 j ⁻¹' gaf07SlimRatio_G47 P.toLocalChartPackets
  isOpen_dom j := (C.slimParam_spec_ZSP35 j).1.continuousOn.isOpen_inter_preimage isOpen_ball
    (isOpen_gaf07SlimRatio_ZSP35 P.toLocalChartPackets)
  param_smooth j := (C.slimParam_spec_ZSP35 j).1.mono inter_subset_left
  coord_param j b hb := ((C.slimParam_spec_ZSP35 j).2.1 b hb.1).2
  piece_relOpen j := by
    obtain ⟨hψ, hin, hout⟩ := C.slimParam_spec_ZSP35 j
    obtain ⟨-, h2⟩ := open_piece_of_chart_BAS _ _ (ρ j.1) (10 ^ 5 * Δ) (C.slimParam_ZSP35 j)
      (C.toChain.finalBase_BAS 2) _ (isOpen_gaf07SlimRatio_ZSP35 P.toLocalChartPackets)
      hψ.continuousOn (fun b hb => (hin b hb).1) hout
    refine ⟨markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∩
        gaf07SlimRatio_G47 P.toLocalChartPackets,
      (isOpen_markedCondition_BPRE _ _ _ _).inter
        (isOpen_gaf07SlimRatio_ZSP35 P.toLocalChartPackets), ?_⟩
    rw [← h2, slimBs_ZSP35]
    ext y
    simp only [mem_inter_iff]
    tauto
  cover := by
    ext y
    constructor
    · rintro ⟨hyW, hyR⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (C.toChain.finalBase_slim_cover_BAS hyW)
      obtain ⟨hb, hψy⟩ := (C.slimParam_spec_ZSP35 j).2.2 y ⟨hyW, hj⟩
      exact mem_iUnion.mpr ⟨j, _, ⟨hb, by rw [mem_preimage, hψy]; exact hyR⟩, hψy⟩
    · intro hy
      obtain ⟨j, b, hb, rfl⟩ := mem_iUnion.mp hy
      exact ⟨((C.slimParam_spec_ZSP35 j).2.1 b hb.1).1.1, hb.2⟩

/-- A threshold-5 slim patch point lies in `W₃` (`Θ₃ = id`). -/
theorem mem_finalBase_of_slimPatch_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.toChain.slimPatch_BAS j) : w ∈ C.toChain.finalBase_BAS 2 :=
  ⟨w, mem_iUnion.mpr ⟨j, hw⟩, rfl⟩

/-- On `Y_j` (`B(c_j, 10⁶Δρ_j)`, `|η_j| < 5·10⁵Δ`), `f₃ = π₃E` lands in `W₃ ∩ {marked j}` and
`ψ_j ∘ g_j = f₃` (`g_j = R_j⁻¹ axis u_j ∘ f₃`, GAF-C's adjusted axis coordinate). -/
theorem slim_param_coord_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset) {q : X}
    (hq : q ∈ gaf07SlimY_GAFC P.toLocalChartPackets j) :
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E q) ∈
        C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∧
      C.toChain.gaf07SlimCoord_GAFC j q ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∧
      C.slimParam_ZSP35 j (C.toChain.gaf07SlimCoord_GAFC j q) =
        (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E q) := by
  have hV := C.toChain.slim_mem_patch_of_domain5_BAS j hq.1 hq.2
  rw [C.stageMap_two_eq_GAFC] at hV
  have hWm : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E q) ∈
      C.toChain.finalBase_BAS 2 ∩ markedCondition_BPRE
        (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) :=
    ⟨C.mem_finalBase_of_slimPatch_ZSP35 j hV, hV.2.1, hV.2.2⟩
  obtain ⟨hb, hψ⟩ := (C.slimParam_spec_ZSP35 j).2.2 _ hWm
  have hco : ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E q)) =
      C.toChain.gaf07SlimCoord_GAFC j q :=
    slim_retained_coord_eq_GAFC (P := P) j _
  rw [hco] at hb hψ
  exact ⟨hWm, hb, hψ⟩

/-- **The slab image lies in the base**: `f₃(⋃_{i ∈ I_s} {|η_i| ≤ 3.5·10⁵Δ}) ⊆ Bs = W₃ ∩ R₃`. -/
theorem slimSlabImage_subset_slimBs_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    C.toChain.slimSlabImage_ZSP35 ⊆ C.slimBs_ZSP35 := by
  obtain ⟨-, -, hR, -⟩ := C.toChain.zsp04_slab_image_ZSP35
  obtain ⟨-, hΔ1, -⟩ := C.toChain.std
  intro w hw
  refine ⟨?_, hR hw⟩
  obtain ⟨p, hp, rfl⟩ := hw
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have hY : p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i := by
    refine ⟨?_, by linarith [hi.2]⟩
    have hb : ball i.1 (1000000 * Δ * ρ i.1) = ball i.1 (10 ^ 6 * Δ * ρ i.1) := by norm_num
    rw [hb]
    exact hi.1
  exact (C.slim_param_coord_ZSP35 i hY).1.1

/-- **ZSP04 (SK), up to the face set** (B:6564–6574, kernel (K-a) of B-BCF134): for EVERY finite
set `F` of base points there are finitely many closed chart intervals `[a_r, b_r] ⊆ dom (c r)`
with endpoints `ψ(a_r), ψ(b_r) ∉ F`, whose union `K'` is compact, lies in `Bs`, and contains the
slab image `f₃(⋃ slabs)` in its relative interior in `Bs`. (`F = ∂C₃` gives (SK).) -/
theorem zsp04_SK_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    {F : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))} (hF : F.Finite) :
    ∃ (n : ℕ) (c' : Fin n → P.slim.finite_centres.toFinset) (a b' : Fin n → ℝ),
      (∀ r, a r < b' r ∧ Icc (a r) (b' r) ⊆ C.slimAtlas_ZSP35.dom (c' r) ∧
        C.slimParam_ZSP35 (c' r) (a r) ∉ F ∧ C.slimParam_ZSP35 (c' r) (b' r) ∉ F) ∧
      IsCompact (⋃ r, C.slimParam_ZSP35 (c' r) '' Icc (a r) (b' r)) ∧
      (⋃ r, C.slimParam_ZSP35 (c' r) '' Icc (a r) (b' r)) ⊆ C.slimBs_ZSP35 ∧
      C.toChain.slimSlabImage_ZSP35 ⊆ Subtype.val '' interior
        (Subtype.val ⁻¹' (⋃ r, C.slimParam_ZSP35 (c' r) '' Icc (a r) (b' r)) :
          Set C.slimBs_ZSP35) := by
  obtain ⟨-, hI, -⟩ := C.toChain.zsp04_slab_image_ZSP35
  obtain ⟨n, c', a, b', hab, hK, hKB, hKi, -⟩ :=
    C.slimAtlas_ZSP35.exists_cover_union_BCF hI C.slimSlabImage_subset_slimBs_ZSP35 hF
      (Dset := ∅) (by simp) (by simp)
  exact ⟨n, c', a, b', hab, hK, hKB, hKi⟩

end Gaf02ChainE

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- The adjusted axis coordinate `g_j` is smooth on `M`. -/
theorem contMDiff_slimCoord_ZSP35 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (j : P.slim.finite_centres.toFinset) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (C.toChain.gaf07SlimCoord_GAFC j) :=
  (((EuclideanSpace.proj (0 : Fin 2)).comp ((ρ j.1)⁻¹ •
    (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inl j))))).comp (gafStageQ P.toLocalChartFamily P.zero 2).starProjection).contDiff
    |>.comp_contMDiff C.toChain.stage_smooth.2.2

/-- **The local chart form of `f₃` at a point of `U = f₃⁻¹(Bs)`**: there is a slim index `i` with
`p ∈ Y_i`, `g_i` a submersion at `p`, and on `Y_i` the identity `f₃ = ψ_i ∘ g_i` with
`g_i ∈ B(0, 5.5·10⁵Δ)` (GAF-C's slim submersion and BASES' threshold-5 patches). -/
theorem slim_chart_local_ZSP35 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) {p : X}
    (hp : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
      C.slimBs_ZSP35) :
    ∃ i : P.slim.finite_centres.toFinset, p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (C.toChain.gaf07SlimCoord_GAFC i) p) ∧
      ∀ q ∈ gaf07SlimY_GAFC P.toLocalChartPackets i,
        C.toChain.gaf07SlimCoord_GAFC i q ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∧
        C.slimParam_ZSP35 i (C.toChain.gaf07SlimCoord_GAFC i q) =
          (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E q) := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp.2
  obtain ⟨hY, hsurj⟩ := C.toChain.gaf07_slim_submersion_GAFC C.c_two_lt i p hi.1 hi.2
  exact ⟨i, hY, hsurj, fun q hq => (C.slim_param_coord_ZSP35 i hq).2⟩

/-- **`U = f₃⁻¹(Bs)` is open in `M`** (it is covered by the open sets `Y_i ∩ f₃⁻¹(R₃)`). -/
theorem isOpen_slimSource_ZSP35 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    IsOpen ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      (C.toChain.E p)) ⁻¹' C.slimBs_ZSP35) := by
  have hcont : Continuous
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) :=
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection.continuous.comp
      C.toChain.stage_smooth.2.2.continuous
  refine isOpen_iff_forall_mem_open.mpr fun p hp => ?_
  obtain ⟨i, hY, -, -⟩ := C.slim_chart_local_ZSP35 hp
  refine ⟨gaf07SlimY_GAFC P.toLocalChartPackets i ∩
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ⁻¹'
        gaf07SlimRatio_G47 P.toLocalChartPackets, fun q hq => ⟨?_, hq.2⟩,
    (isOpen_gaf07SlimY_GAFC P.toLocalChartPackets i).inter
      ((isOpen_gaf07SlimRatio_ZSP35 P.toLocalChartPackets).preimage hcont), hY, hp.2⟩
  exact (C.slim_param_coord_ZSP35 i hq.1).1.1

/-- **`f₃|U` is open onto `Bs`** (the kernel's input (I1), closed side): the image of every open
subset of `U = f₃⁻¹(Bs)` is relatively open in `Bs`. -/
theorem slim_relOpen_ZSP35 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) {W : Set X}
    (hWU : W ⊆ (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      (C.toChain.E p)) ⁻¹' C.slimBs_ZSP35) (hW : IsOpen W) :
    ∃ O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen O ∧
      O ∩ C.slimBs_ZSP35 =
        (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ''
          W := by
  have hloc : ∀ p ∈ W, ∃ O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      IsOpen O ∧ (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈ O ∧
      O ∩ C.slimBs_ZSP35 ⊆
        (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ''
          W := by
    intro p hpW
    obtain ⟨i, hY, hsurj, hloc⟩ := C.slim_chart_local_ZSP35 (hWU hpW)
    have hmap := DifferentialGeometry.Topology.map_nhds_eq_of_mfderiv_surjective_at
      (((C.contMDiff_slimCoord_ZSP35 i) p).of_le (by simp)) hsurj
    have hN : W ∩ gaf07SlimY_GAFC P.toLocalChartPackets i ∈ 𝓝 p :=
      (hW.inter (isOpen_gaf07SlimY_GAFC P.toLocalChartPackets i)).mem_nhds ⟨hpW, hY⟩
    have himg : C.toChain.gaf07SlimCoord_GAFC i '' (W ∩ gaf07SlimY_GAFC P.toLocalChartPackets i) ∈
        𝓝 (C.toChain.gaf07SlimCoord_GAFC i p) := by
      rw [← hmap]
      exact image_mem_map hN
    obtain ⟨O', hO'sub, hO', hpO'⟩ := _root_.mem_nhds_iff.mp himg
    have hO'dom : O' ⊆ C.slimAtlas_ZSP35.dom i := by
      intro t ht
      obtain ⟨q, ⟨hqW, hqY⟩, rfl⟩ := hO'sub ht
      obtain ⟨hb, hψ⟩ := hloc q hqY
      refine ⟨hb, ?_⟩
      change C.slimParam_ZSP35 i (C.toChain.gaf07SlimCoord_GAFC i q) ∈
        gaf07SlimRatio_G47 P.toLocalChartPackets
      rw [hψ]
      exact (hWU hqW).2
    obtain ⟨O, hO, hOB⟩ := C.slimAtlas_ZSP35.image_relOpen_BCF hO' hO'dom
    refine ⟨O, hO, ?_, ?_⟩
    · have hmem : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
          O ∩ C.slimBs_ZSP35 := by
        rw [hOB]
        exact ⟨_, hpO', (hloc p hY).2⟩
      exact hmem.1
    · rw [hOB]
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨q, ⟨hqW, hqY⟩, rfl⟩ := hO'sub ht
      exact ⟨q, hqW, ((hloc q hqY).2).symm⟩
  choose! O hO hpO hOsub using hloc
  refine ⟨⋃ p ∈ W, O p, isOpen_biUnion fun p hp => hO p hp, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, hwB⟩
    obtain ⟨p, hp, hwp⟩ := mem_iUnion₂.mp hw
    exact hOsub p hp ⟨hwp, hwB⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨mem_iUnion₂.mpr ⟨p, hp, hpO p hp⟩, hWU hp⟩

end Gaf02ChainEJA

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **Consumer: ZSP04's (SK) and the openness of `f₃` on the final family** (chain with (JA) on
the `C14` projection of `LocalChartPacketsC14Z`): `U = f₃⁻¹(Bs)` is open, `f₃|U` is open onto
`Bs`, and for every finite `F` a compact finite union of closed chart intervals `K' ⊆ Bs`, with
endpoints off `F`, contains the slab image in its relative interior. -/
theorem zsp04_SK_C14Z_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    {F : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))} (hF : F.Finite) :
    IsOpen ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      (C.toChain.E p)) ⁻¹' C.slimBs_ZSP35) ∧
    (∀ W : Set X, W ⊆ (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        (C.toChain.E p)) ⁻¹' C.slimBs_ZSP35 → IsOpen W →
      ∃ O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen O ∧
        O ∩ C.slimBs_ZSP35 =
          (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ''
            W) ∧
    ∃ K' : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      IsCompact K' ∧ K' ⊆ C.slimBs_ZSP35 ∧
      C.toChain.slimSlabImage_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K' : Set C.slimBs_ZSP35) := by
  obtain ⟨n, c', a, b', -, hK, hKB, hKi⟩ := C.toGaf02ChainE.zsp04_SK_ZSP35 hF
  exact ⟨C.isOpen_slimSource_ZSP35, fun W hWU hW => C.slim_relOpen_ZSP35 hWU hW, _, hK, hKB, hKi⟩

end Final

end DifferentialGeometry.Geometry.Collapse
