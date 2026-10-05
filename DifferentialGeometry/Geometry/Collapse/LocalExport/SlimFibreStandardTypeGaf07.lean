import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimFibreStandardTypeApplications

/-!
# GAF07's `j = 3` clause in the standard smooth form (review 70, D70-4)

Lane C14-SLIM-STD, group 4 (external review 70 §3.4, last paragraphs; disposition D70-4). The strong
GAF07 consumer: C14-FIBRE-PRE's `SlimPacket.gaf07_slim_fibre_type_FPRE` gives, for a smooth family
`h` on a slab starting at the ORIGINAL coordinate, regular along the level `a` for `τ ∈ [0, 1]`
with compact trace (FC34's transport), a diffeomorphism `d₀₁ : F₀ ≃ₘ F₁` from the original zero
fibre onto the WHOLE end level `F₁ = {h(·, 1) = a}`. Composing `d₀₁⁻¹` with D70-2's standard
identification of `F₀` gives `F₁ ≃ₘ ClosureSphere` or `F₁ ≃ₘ Torus`. The weak theorem stays; the
smooth homotopy, the regularity along the whole path and the compact trace are kept as hypotheses
(the inputs of FC34, as in the weak form).

* `SlimPacket.gaf07_slim_fibre_standard_type_SSTD`: for a slim packet `P` (`K ≥ 5`, `Δ ≥ 1`), a
  product model `PM : SlimProductModel P.toSlimChart K` and an orientation `oM` of the manifold:
  `F₀ ≃ₘ F₁`, `F₁` compact and connected, and `F₁ ≃ₘ ClosureSphere ∨ F₁ ≃ₘ Torus`.
* consumer `SlimCentre.gaf07_slim_fibre_standard_type_SSTD`: the same at a slim centre of the final
  family (`SlimCentre`, the stored packet and the stored model, the normalized instances), for the
  family's orientation parameter.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model of the slim fibres (`dim M - 1`). -/
local notation "𝓘S" => 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ)

universe u

section Packet

variable {M : Type*} [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M} {hEnorm : IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}

/-- **GAF07's `j = 3` clause, standard smooth form.** Let `P` be a slim packet (`K ≥ 5`, `Δ ≥ 1`)
with an LC81 product model `PM` over a manifold with an orientation `oM`, and let
`h : Y × ℝ → ℝ` be a smooth family on the slab `Y = {x ∈ B(p, L) | |η x| < r}` (`r ≤ 905·10³Δ`)
with `h(·, 0) = η`, regular along the level `a` (`|a| < r`) for `τ ∈ [0, 1]`, with its whole trace
in one compact set. Then the WHOLE end level `F₁ = {h(·, 1) = a}` (regular-fibre structure) is
diffeomorphic to the original zero fibre `F₀`, compact, connected, and diffeomorphic to the standard
`ClosureSphere` or `Torus`. -/
theorem SlimPacket.gaf07_slim_fibre_standard_type_SSTD (P : SlimPacket g hEnorm Δ σ α) {K : ℕ}
    (hK : 5 ≤ K) (hΔ : 1 ≤ Δ) (PM : SlimProductModel P.toSlimChart K)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) M 3) {r : ℝ} (hr : r ≤ 905 * 10 ^ 3 * Δ)
    (a : lineBallOpens r)
    (h : realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball P.coord
      P.lipschitz.continuous.continuousOn r × ℝ → ℝ)
    (hh : ContMDiff (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ) ∞ h) (h0 : ∀ y, h (y, 0) = P.coord y.1)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a.1 →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z => h (z, τ)) y))
    {Q : Set (realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball P.coord
      P.lipschitz.continuous.continuousOn r)} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a.1 → y ∈ Q) :
    letI := P.fibreChartedSpace_FPRE le_rfl
      (SlimChart.zeroPoint_FPRE (lt_of_lt_of_le zero_lt_one hΔ))
    letI := regularFiberChartedSpace (fun y => h (y, 1)) a.1 (contMDiff_familySlice hh 1)
      (hreg 1 (right_mem_Icc.mpr zero_le_one))
    Nonempty ({x // P.slabMap_FPRE (905 * 10 ^ 3 * Δ) x =
        SlimChart.zeroPoint_FPRE (lt_of_lt_of_le zero_lt_one hΔ)} ≃ₘ⟮𝓘S, 𝓘S⟯
          {y // h (y, 1) = a.1}) ∧
      CompactSpace {y // h (y, 1) = a.1} ∧ ConnectedSpace {y // h (y, 1) = a.1} ∧
      (Nonempty ({y // h (y, 1) = a.1} ≃ₘ⟮𝓘S, 𝓡 2⟯ ClosureSphere.{u}) ∨
        Nonempty ({y // h (y, 1) = a.1} ≃ₘ⟮𝓘S, torusModel⟯ Torus)) := by
  have hΔ0 : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  let _ := P.fibreChartedSpace_FPRE le_rfl (SlimChart.zeroPoint_FPRE hΔ0)
  let _ := regularFiberChartedSpace (fun y => h (y, 1)) a.1 (contMDiff_familySlice hh 1)
    (hreg 1 (right_mem_Icc.mpr zero_le_one))
  obtain ⟨⟨d₀₁⟩, hcpt, hconn, -⟩ := P.gaf07_slim_fibre_type_FPRE hΔ0 hr a h hh h0 hreg hQ hloc
  obtain ⟨Q'⟩ := PM.nonempty_slimSurfaceFactor_of_oriented_source_SSTD hK hΔ oM
  refine ⟨⟨d₀₁⟩, hcpt, hconn, ?_⟩
  rcases P.toSlimChart.zero_fibre_standard_type_SSTD.{u} hK hΔ PM Q' with ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩
  · exact Or.inl ⟨d₀₁.symm.trans d⟩
  · exact Or.inr ⟨d₀₁.symm.trans d⟩

end Packet

section Centre

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

/-- **Consumer: GAF07's standard fibre type at a slim centre of the final family.** At a slim
centre `j` (`K ≥ 5`, `Δ ≥ 1`) of a manifold with orientation `oM`, for the STORED packet and model
of the centre (normalized instances `(ρ(j)⁻¹ d, ρ(j)⁻² g)`): every FC34 end level `{h(·, 1) = a}`
of a regular family on a slab of the packet starting at the original coordinate, with compact
trace, is diffeomorphic to the standard `ClosureSphere` or `Torus`. -/
theorem SlimCentre.gaf07_slim_fibre_standard_type_SSTD
    (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) (hK : 5 ≤ K) (hΔ : 1 ≤ Δ)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3) :
    let P := c.packet
    letI := c.instZ
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    ∀ {r : ℝ} (_ : r ≤ 905 * 10 ^ 3 * Δ) (a : lineBallOpens r)
      (h : realSlabOpens (ball j (10 ^ 6 * Δ)) isOpen_ball P.coord
        P.lipschitz.continuous.continuousOn r × ℝ → ℝ)
      (hh : ContMDiff (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ) ∞ h) (_ : ∀ y, h (y, 0) = P.coord y.1)
      (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a.1 →
        Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z => h (z, τ)) y))
      {Q : Set (realSlabOpens (ball j (10 ^ 6 * Δ)) isOpen_ball P.coord
        P.lipschitz.continuous.continuousOn r)} (_ : IsCompact Q)
      (_ : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a.1 → y ∈ Q),
      letI := regularFiberChartedSpace (fun y => h (y, 1)) a.1 (contMDiff_familySlice hh 1)
        (hreg 1 (right_mem_Icc.mpr zero_le_one))
      Nonempty ({y // h (y, 1) = a.1} ≃ₘ⟮𝓘S, 𝓡 2⟯ ClosureSphere.{0}) ∨
        Nonempty ({y // h (y, 1) = a.1} ≃ₘ⟮𝓘S, torusModel⟯ Torus) := by
  have PM := c.model
  intro P hMc r hr a h hh h0 hreg Q hQ hloc
  let iZ := c.instZ
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact (P.gaf07_slim_fibre_standard_type_SSTD hK hΔ PM oM hr a h hh h0 hreg hQ hloc).2.2.2

end Centre

end DifferentialGeometry.Geometry.Collapse
