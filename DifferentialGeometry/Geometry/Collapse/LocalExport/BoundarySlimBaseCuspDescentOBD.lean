import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimBaseCuspEquationOBD
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential

/-!
# BCG07 07.g3 in the shape of review 77 (D77-6): the descended cusp function along the ACTUAL base

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G3d. D77-6: 07.g3 is the DESCENDED function
`h_b = u_b/v_b − 40` on the slim base, with non-zero differential ALONG THE ACTUAL BASE, obtained
by descent + chain rule + rank (a non-zero differential of an ambient extension is not enough).

* descent: `cuspRatioBase_OBD b y = (J_b y)¹/(J_b y)² − 40` on `H^∂`; since every stage projection
  keeps every boundary slot, `h_b ∘ f_j = u_b/v_b − 40` on the whole carrier
  (`cuspRatioBase_stageMap_OBD`); `h_b` restricted to `B₃` is the descended function;
* rank (generic): `fderiv_ne_zero_of_comp_fst_OBD` — if `G ∘ φ = h ∘ pr₁` for a local
  diffeomorphism `φ : ℝᵏ × F → M` (surjective differential) and `dG ≠ 0`, then `dh ≠ 0`;
* **`BoundaryGaf02ChainE.cuspRatio_baseChart_OBD`** (A4 data, E4b): at every point `p` of the cusp
  front in `X₃`, in the ACTUAL base chart `σ : ℝ → B₃` of `WF.slim_chart` at `f₃ p` (smooth
  embedding with injective derivative, `range σ = B₃ ∩ O`), `(h_b ∘ σ)′(0) ≠ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Rank

variable {EM HM M EF HF F : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  [TopologicalSpace F] [ChartedSpace HF F] {k : ℕ}

/-- **Rank argument**: if `G ∘ φ = h ∘ pr₁` where `φ : ℝᵏ × F → M` has surjective differential
at `x₀` and `G` has non-zero differential at `φ x₀`, then `h` has non-zero derivative at the base
point `x₀.1`. -/
theorem fderiv_ne_zero_of_comp_fst_OBD {φ : EuclideanSpace ℝ (Fin k) × F → M} {G : M → ℝ}
    {h : EuclideanSpace ℝ (Fin k) → ℝ} {x₀ : EuclideanSpace ℝ (Fin k) × F}
    (hφ : MDifferentiableAt ((𝓡 k).prod IF) IM φ x₀)
    (hφs : Surjective (mfderiv ((𝓡 k).prod IF) IM φ x₀))
    (hG : MDifferentiableAt IM 𝓘(ℝ, ℝ) G (φ x₀)) (hG0 : mfderiv IM 𝓘(ℝ, ℝ) G (φ x₀) ≠ 0)
    (hcomp : ∀ x, G (φ x) = h x.1) : fderiv ℝ h x₀.1 ≠ 0 := by
  intro h0
  apply hG0
  have hmk : MDifferentiableAt (𝓡 k) ((𝓡 k).prod IF) (fun t => (t, x₀.2)) x₀.1 :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hd : MDifferentiableAt (𝓡 k) 𝓘(ℝ, ℝ) h x₀.1 := by
    have h1 : MDifferentiableAt (𝓡 k) 𝓘(ℝ, ℝ) (G ∘ φ ∘ fun t => (t, x₀.2)) x₀.1 :=
      hG.comp x₀.1 (hφ.comp x₀.1 hmk)
    have h2 : (G ∘ φ ∘ fun t => (t, x₀.2)) = h := funext fun t => hcomp (t, x₀.2)
    rwa [h2] at h1
  have e1 : mfderiv ((𝓡 k).prod IF) 𝓘(ℝ, ℝ) (G ∘ φ) x₀ =
      (mfderiv IM 𝓘(ℝ, ℝ) G (φ x₀)).comp (mfderiv ((𝓡 k).prod IF) IM φ x₀) :=
    mfderiv_comp x₀ hG hφ
  have e2 : mfderiv ((𝓡 k).prod IF) 𝓘(ℝ, ℝ) (h ∘ Prod.fst) x₀ =
      (mfderiv (𝓡 k) 𝓘(ℝ, ℝ) h x₀.1).comp (mfderiv ((𝓡 k).prod IF) (𝓡 k) Prod.fst x₀) :=
    mfderiv_comp x₀ hd mdifferentiableAt_fst
  have e3 : G ∘ φ = h ∘ Prod.fst := funext hcomp
  have hz : mfderiv (𝓡 k) 𝓘(ℝ, ℝ) h x₀.1 = 0 := by
    rw [mfderiv_eq_fderiv]
    exact h0
  have hc : (mfderiv IM 𝓘(ℝ, ℝ) G (φ x₀)).comp (mfderiv ((𝓡 k).prod IF) IM φ x₀) = 0 := by
    rw [← e1, e3, e2, hz]
    exact ContinuousLinearMap.zero_comp _
  ext w
  obtain ⟨v, rfl⟩ := hφs w
  exact congrArg (fun L => L v) hc

end Rank

section Generic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The descended cusp function** `h_b = (J_b)¹/(J_b)² − 40` on the ambient base. -/
def cuspRatioBase_OBD (b : κ) (y : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) : ℝ :=
  (augmentedBoundaryCoord_BC7C b y).1 / (augmentedBoundaryCoord_BC7C b y).2 - 40

end Generic

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **Descent**: `h_b ∘ f_j = u_b/v_b − 40` on the whole carrier, every stage. -/
theorem cuspRatioBase_stageMap_OBD (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
    (st : Fin 3) (i : Fin S.packet.cusp.count) (p : W.Carrier) :
    cuspRatioBase_OBD i (C.stageMap st p) =
      chainBoundaryU_BCG6K C.E i p / chainBoundaryV_BCG6K C.E i p - 40 := by
  simp only [cuspRatioBase_OBD, augmentedBoundaryCoord_BC7C, BoundaryGaf02Chain.stageMap,
    Φ.stageProj_inr_BGR]
  rfl

end Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- Near a front point, `u_b/v_b − 40` agrees with `u_b − 40 v_b`; it is differentiable there
with non-zero differential (E4b). -/
theorem cuspRatio_regular_at_front_OBD {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) {p : W.Carrier}
    (hp : p ∈ C.toChain.cuspFront_BIF i) :
    MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun q => chainBoundaryU_BCG6K C.toChain.E i q /
        chainBoundaryV_BCG6K C.toChain.E i q - 40) p ∧
      mfderiv W.model 𝓘(ℝ, ℝ) (fun q => chainBoundaryU_BCG6K C.toChain.E i q /
        chainBoundaryV_BCG6K C.toChain.E i q - 40) p ≠ 0 := by
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have heq : (fun q => chainBoundaryU_BCG6K C.toChain.E i q /
      chainBoundaryV_BCG6K C.toChain.E i q - 40) =ᶠ[𝓝 p]
      fun q => chainBoundaryU_BCG6K C.toChain.E i q -
        40 * chainBoundaryV_BCG6K C.toChain.E i q := by
    filter_upwards [hspec.marker_eq_one_near_front i p hp] with q hq
    rw [hq, div_one, mul_one]
  have hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryU_BCG6K C.toChain.E i) :=
    contMDiff_chainBoundaryU_BCG6K (C.stage_smooth_BAUGD 3) i
  have hv : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryV_BCG6K C.toChain.E i) :=
    (chainBoundaryVCLM_OBD (ι := S.IntTag_BAUGA) i).contDiff.comp_contMDiff
      (C.stage_smooth_BAUGD 3)
  have hsm : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun q => chainBoundaryU_BCG6K C.toChain.E i q -
      40 * chainBoundaryV_BCG6K C.toChain.E i q) p :=
    ((hu.sub (contMDiff_const.mul hv)) p).mdifferentiableAt (by simp)
  refine ⟨hsm.congr_of_eventuallyEq heq, ?_⟩
  rw [heq.mfderiv_eq]
  exact hspec.defining_differential_ne_zero i p hp

/-- **07.g3 in one actual base chart** (D77-6): for a front point `p ∈ X₃` and a smooth product
chart of `f₃` at `f₃ p` with fibre model `F` (dimension count `1 + dim F = 3`), the descended
`h_b` has non-zero derivative along the base chart `σ` at `0`. -/
theorem cuspRatio_baseChart_of_chart_OBD {EF HF F : Type*} [NormedAddCommGroup EF]
    [NormedSpace ℝ EF] [FiniteDimensional ℝ EF] [TopologicalSpace HF]
    {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F]
    (hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EF) = Module.finrank ℝ E3)
    {Bs : BoundaryGaf02BasesV2 C.toChain} {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) {p : W.Carrier}
    (hp : p ∈ C.toChain.cuspFront_BIF i) (hpX : p ∈ Bs.source 2)
    (hch : SmoothProductChartAt_BIFc W.model IF (F := F) 1 (C.toChain.stageMap 2) (Bs.source 2)
      (Bs.base 2) (C.toChain.stageMap 2 p)) :
    ∃ σ : EuclideanSpace ℝ (Fin 1) → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count),
      σ 0 = C.toChain.stageMap 2 p ∧ ContDiff ℝ ∞ σ ∧ Topology.IsEmbedding σ ∧
      (∀ x, Injective (fderiv ℝ σ x)) ∧
      (∃ O, IsOpen O ∧ range σ = Bs.base 2 ∩ O) ∧ fderiv ℝ (cuspRatioBase_OBD i ∘ σ) 0 ≠ 0 := by
  obtain ⟨σ, φ, O, h0, hσs, hσe, hσd, hO, hr, hφ, hrφ, hf⟩ := hch
  have hpφ : p ∈ range φ := by
    rw [hrφ]
    exact ⟨hpX, 0, h0⟩
  obtain ⟨x₀, hx₀⟩ := hpφ
  have hx₀1 : x₀.1 = 0 := by
    have h1 : C.toChain.stageMap 2 (φ (x₀.1, x₀.2)) = σ x₀.1 := hf x₀.1 x₀.2
    have h2 : C.toChain.stageMap 2 (φ x₀) = σ 0 := by rw [hx₀, h0]
    exact hσe.injective (h1.symm.trans h2)
  obtain ⟨hGd, hG0⟩ := C.cuspRatio_regular_at_front_OBD hrd hrd4 hrdc hprem hθ i hp
  have hcomp : ∀ x, (fun q => chainBoundaryU_BCG6K C.toChain.E i q /
      chainBoundaryV_BCG6K C.toChain.E i q - 40) (φ x) = (cuspRatioBase_OBD i ∘ σ) x.1 :=
    fun x => by
      change _ = cuspRatioBase_OBD i (σ x.1)
      rw [← hf x.1 x.2, cuspRatioBase_stageMap_OBD C.toChain 2 i]
  have hφd : MDifferentiableAt ((𝓡 1).prod IF) W.model φ x₀ :=
    hφ.contMDiff.mdifferentiableAt (by simp)
  have hφs : Surjective (mfderiv ((𝓡 1).prod IF) W.model φ x₀) :=
    (bijective_mfderiv_of_isImmersionAt ((𝓡 1).prod IF) W.model φ x₀
      (hφ.isImmersion.isImmersionAt x₀) hdim).2
  rw [← hx₀] at hGd hG0
  have hne := fderiv_ne_zero_of_comp_fst_OBD hφd hφs hGd hG0 hcomp
  rw [hx₀1] at hne
  exact ⟨σ, h0, hσs, hσe, hσd, ⟨O, hO, hr⟩, hne⟩

/-- **BCG07 07.g3, review 77 shape** (A4 data `Bs`, `WF` v2b; E4b premises): at every front point
`p ∈ H_b ∩ X₃`, in the ACTUAL base chart `σ` of `WF.slim_chart` at `f₃ p` (smooth embedding into
`H^∂`, injective derivative, `range σ = B₃ ∩ O`), the descended cusp function `h_b` (with
`h_b ∘ f₃ = u_b/v_b − 40`) has non-zero derivative: `(h_b ∘ σ)′(0) ≠ 0`. -/
theorem cuspRatio_baseChart_OBD {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) {p : W.Carrier}
    (hp : p ∈ C.toChain.cuspFront_BIF i) (hpX : p ∈ Bs.source 2) :
    ∃ σ : EuclideanSpace ℝ (Fin 1) → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count),
      σ 0 = C.toChain.stageMap 2 p ∧ ContDiff ℝ ∞ σ ∧ Topology.IsEmbedding σ ∧
      (∀ x, Injective (fderiv ℝ σ x)) ∧
      (∃ O, IsOpen O ∧ range σ = Bs.base 2 ∩ O) ∧ fderiv ℝ (cuspRatioBase_OBD i ∘ σ) 0 ≠ 0 := by
  have hy : C.toChain.stageMap 2 p ∈ Bs.base 2 := by
    rw [← Bs.image_eq 2]
    exact mem_image_of_mem _ hpX
  rcases WF.slim_chart _ hy with hch | hch
  · exact C.cuspRatio_baseChart_of_chart_OBD (by simp) hrd hrd4 hrdc hprem hθ i hp hpX hch
  · exact C.cuspRatio_baseChart_of_chart_OBD (by simp) hrd hrd4 hrdc hprem hθ i hp hpX hch

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
