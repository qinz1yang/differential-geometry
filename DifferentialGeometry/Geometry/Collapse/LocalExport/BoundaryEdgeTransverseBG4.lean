import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornerIndependenceG6C

/-!
# BCF02 G4, group G2: smoothness, regularity and transversality of `h ∘ f₂` (lane S-BCF02-G4)

Three facts about a face function `h : H → ℝ` pulled back by the edge stage map `f₂`, used for the
fields `face_smooth`, `regular`, `transverse` of `BoundaryRelativeEdgeRestrictionV2`:

* `mvfderiv_congr_nhds_BG4`: `mvfderiv` of two real functions that agree near `p` agree at `p`;
* `contMDiffAt_comp_stageMap_BG4`: `h` smooth at `f₂ p` gives `h ∘ f₂` smooth at `p`;
* **`surjective_comp_height_BG4`**: for `p` in the open edge parent with `T = 4Δ`, if `h` is
  differentiable at `f₂ p` and `d(h ∘ f₂) ≠ 0` at `p`, then `(d(h ∘ f₂), dT)` is onto `ℝ²`
  (`rank df₂ = 1`, `rank d(f₂, T) = 2`: the kernel of `df₂` is a plane on which `d(h ∘ f₂)`
  vanishes; consumer: `surjective_faceFun_height_of_plane_G6C`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- `mvfderiv` of two real functions that agree near `x` agree at `x`. -/
theorem mvfderiv_congr_nhds_BG4 {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
    {f g : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] g) : mvfderiv I f x = mvfderiv I g x := by
  refine ContinuousLinearMap.ext fun V => ?_
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv I f x V,
    DifferentialGeometry.mvfderiv_real_eq_mfderiv I g x V,
    Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) h]
  rfl

namespace BoundaryGaf02ChainE

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- `h` smooth at `f₂ p` gives `h ∘ f₂` smooth at `p` (`f₂` is smooth on all of `W`). -/
theorem contMDiffAt_comp_stageMap_BG4 {p : W.Carrier}
    {h : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ}
    (hh : ContDiffAt ℝ ∞ h (C.toChain.stageMap 1 p)) :
    ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun q => h (C.toChain.stageMap 1 q)) p :=
  hh.contMDiffAt.comp p (C.stageMap_contMDiff_BAUGD 1 p)

/-- **Transversality of a pulled-back face function with the height** (fields `transverse`):
at `p` in the open edge parent with `T = 4Δ`, if `h` is differentiable at `f₂ p` and
`d(h ∘ f₂) ≠ 0` then `(d(h ∘ f₂), dT)` is onto `ℝ²`. -/
theorem surjective_comp_height_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain} {p : W.Carrier}
    (hp : p ∈ Bs.edgeParent) (hT : C.toChain.heightRatio p = 4 * Δ)
    {h : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ}
    (hh : DifferentiableAt ℝ h (C.toChain.stageMap 1 p))
    (hreg : mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p ≠ 0) :
    Surjective fun v : TangentSpace W.model p =>
      (mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p v,
        mvfderiv W.model C.toChain.heightRatio p v) := by
  have hf : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stageMap 1) p :=
    (C.stageMap_contMDiff_BAUGD 1 p).mdifferentiableAt (by simp)
  have hrank : C.toChain.stageRank_BIFc 1 p = 1 := Bs.parent.edgeParent_rank p hp
  let L : TangentSpace W.model p →ₗ[ℝ]
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
    (mvfderiv W.model (C.toChain.stageMap 1) p :
      TangentSpace W.model p →L[ℝ] BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
  have hdim : Module.finrank ℝ (TangentSpace W.model p) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    exact finrank_euclideanSpace_fin
  have hP : Module.finrank ℝ (LinearMap.ker L) = 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    have h2 : Module.finrank ℝ (LinearMap.range L) = 1 := hrank
    omega
  refine C.surjective_faceFun_height_of_plane_G6C hp hT _ hreg (LinearMap.ker L) hP ?_
    (fun w hw => LinearMap.mem_ker.mp hw)
  intro w hw
  have hc := mvfderiv_comp_apply_of_differentiableAt_GAF3 (I := W.model) hf hh w
  have h0 : mvfderiv W.model (C.toChain.stageMap 1) p w = 0 := LinearMap.mem_ker.mp hw
  change mvfderiv W.model (h ∘ C.toChain.stageMap 1) p w = 0
  rw [hc, h0, map_zero]

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
