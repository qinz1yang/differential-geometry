import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersVerticalConfigG6C

/-!
# G6c corners: independence of a face function and `T` from a vanishing plane (lane O-G6C, G2h)

* `surjective_pair_of_witnesses_G6C`: two functionals `c, b` with `c u ≠ 0` and some `w` with
  `c w = 0`, `b w ≠ 0` are jointly onto `ℝ²`;
* `exists_mem_ne_zero_of_finrank_range_G6C`: if `rank (A, b) = 2`, `dim V = 3` and `A` vanishes on a
  plane `P`, then `b` does not vanish on `P`;
* **`BoundaryGaf02ChainE.surjective_faceFun_height_of_plane_G6C`**: at a rim point of the edge
  parent, a face function `F` with `dF ≠ 0` whose differential vanishes on a plane on which `df₂`
  vanishes (the tangent plane of the edge disk) has `(dF, dT)` onto `ℝ²` (`rank d(f₂, T) = 2`).
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

/-- **Two functionals with witnesses are jointly onto `ℝ²`.** -/
theorem surjective_pair_of_witnesses_G6C {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c b : V →ₗ[ℝ] ℝ) {u w : V} (hu : c u ≠ 0) (hw : c w = 0) (hbw : b w ≠ 0) :
    Surjective fun v : V => (c v, b v) := by
  intro ⟨α, β⟩
  refine ⟨(α / c u) • u + ((β - α / c u * b u) / b w) • w, ?_⟩
  simp only [map_add, map_smul, smul_eq_mul, hw, mul_zero, add_zero, Prod.mk.injEq]
  constructor
  · field_simp
  · field_simp
    ring

/-- **A rank-two pair does not vanish on a plane of a three-space.** -/
theorem exists_mem_ne_zero_of_finrank_range_G6C {V F : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup F] [Module ℝ F] (A : V →ₗ[ℝ] F) (b : V →ₗ[ℝ] ℝ)
    (hV : Module.finrank ℝ V = 3) (P : Submodule ℝ V) (hP : Module.finrank ℝ P = 2)
    (hA : ∀ w ∈ P, A w = 0) (hrk : Module.finrank ℝ (LinearMap.range (A.prod b)) = 2) :
    ∃ w ∈ P, b w ≠ 0 := by
  by_contra h
  have h' : ∀ w ∈ P, b w = 0 := fun w hw => not_not.mp fun hb => h ⟨w, hw, hb⟩
  have hker : P ≤ LinearMap.ker (A.prod b) := fun w hw =>
    LinearMap.mem_ker.mpr (Prod.ext (hA w hw) (h' w hw))
  have h1 := LinearMap.finrank_range_add_finrank_ker (A.prod b)
  have h2 := Submodule.finrank_mono hker
  omega

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **Corner independence from a vanishing plane.** -/
theorem surjective_faceFun_height_of_plane_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    {p : W.Carrier} (hp : p ∈ Bs.edgeParent) (hT : C.toChain.heightRatio p = 4 * Δ)
    (Fn : W.Carrier → ℝ) (hFn : mvfderiv W.model Fn p ≠ 0)
    (P : Submodule ℝ (TangentSpace W.model p)) (hP : Module.finrank ℝ P = 2)
    (hFP : ∀ w ∈ P, mvfderiv W.model Fn p w = 0)
    (hfP : ∀ w ∈ P, mvfderiv W.model (C.toChain.stageMap 1) p w = 0) :
    Surjective fun v : TangentSpace W.model p =>
      (mvfderiv W.model Fn p v, mvfderiv W.model C.toChain.heightRatio p v) := by
  have hrk2 := Bs.parent.edgeParent_rank_two p hp hT
  have hf : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stageMap 1) p :=
    (C.stageMap_contMDiff_BAUGD 1 p).mdifferentiableAt (by simp)
  have hTd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio p :=
    (C.heightRatio_contMDiff_BAUGD p).mdifferentiableAt (by simp)
  have hpair : (mvfderiv W.model
      (fun q => (C.toChain.stageMap 1 q, C.toChain.heightRatio q)) p :
        TangentSpace W.model p →L[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ) =
      (mvfderiv W.model (C.toChain.stageMap 1) p).prod (mvfderiv W.model C.toChain.heightRatio p) :=
    ContinuousLinearMap.ext fun v => mvfderiv_pair_BAUGD hf hTd v
  have hc := congrArg (fun L : TangentSpace W.model p →L[ℝ]
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ =>
    Module.finrank ℝ (LinearMap.range (L : TangentSpace W.model p →ₗ[ℝ]
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ))) hpair
  have h2 : Module.finrank ℝ (LinearMap.range ((mvfderiv W.model
      (fun q => (C.toChain.stageMap 1 q, C.toChain.heightRatio q)) p :
        TangentSpace W.model p →L[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ) :
      TangentSpace W.model p →ₗ[ℝ]
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ)) = 2 := hrk2
  have hrk : Module.finrank ℝ (LinearMap.range
      (((mvfderiv W.model (C.toChain.stageMap 1) p : TangentSpace W.model p →L[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
        TangentSpace W.model p →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)).prod
        (mvfderiv W.model C.toChain.heightRatio p : TangentSpace W.model p →ₗ[ℝ] ℝ))) = 2 := by
    rw [ContinuousLinearMap.coe_prod] at hc
    exact hc.symm.trans h2
  have hdim : Module.finrank ℝ (TangentSpace W.model p) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    exact finrank_euclideanSpace_fin
  obtain ⟨w, hwP, hbw⟩ := exists_mem_ne_zero_of_finrank_range_G6C _ _ hdim P hP hfP hrk
  obtain ⟨u, hu⟩ : ∃ u, mvfderiv W.model Fn p u ≠ 0 := by
    by_contra h
    exact hFn (ContinuousLinearMap.ext fun u => not_not.mp fun hu => h ⟨u, hu⟩)
  exact surjective_pair_of_witnesses_G6C (mvfderiv W.model Fn p : TangentSpace W.model p →ₗ[ℝ] ℝ)
    (mvfderiv W.model C.toChain.heightRatio p : TangentSpace W.model p →ₗ[ℝ] ℝ) hu
    (hFP w hwP) hbw

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
