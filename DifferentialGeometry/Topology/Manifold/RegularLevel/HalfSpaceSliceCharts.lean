import DifferentialGeometry.Topology.Manifold.RegularLevel.HalfSpaceSlice
import DifferentialGeometry.Topology.Manifold.RegularZero.Coordinates
import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Half-space slice charts from the implicit function theorem

Producers of the slice charts consumed by `sliceChartedSpace`: at an interior point of the
ambient manifold (possibly with boundary), submersion coordinates for `Ψ` (when `0 < B x`, height
`0`) or for `(Ψ, B)` (when `B x = 0`, height `1`), followed by an affine rearrangement and the
inverse of `𝓡∂` on the open half-space; at a point of `∂M` (ambient model `𝓡∂`), the ambient
chart restricted, times `ℝ⁰`.
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.RegularLevel
section Producers

/-- An affine diffeomorphism `v ↦ A v + t` of normed spaces. -/
def sliceAffine {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (A : V ≃L[ℝ] W) (t : W) : Diffeomorph 𝓘(ℝ, V) 𝓘(ℝ, W) V W ∞ where
  toFun v := A v + t
  invFun w := A.symm (w - t)
  left_inv v := by simp
  right_inv w := by simp
  contMDiff_toFun := (A.contDiff.add contDiff_const).contMDiff
  contMDiff_invFun := (A.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff

theorem sliceAffine_apply {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (A : V ≃L[ℝ] W) (t : W) (v : V) :
    sliceAffine A t v = A v + t := rfl

variable {d : ℕ} (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `z ↦ (𝓡∂.symm z.1, z.2)` from `{z | 0 < z.1₀}` onto `{q | 0 < q.1₀}`. -/
def sliceHalfSpaceProd :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)) × G) ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G))
      (EuclideanSpace ℝ (Fin (d + 1)) × G) (EuclideanHalfSpace (d + 1) × G) ∞ where
  toFun z := ((𝓡∂ (d + 1)).symm z.1, z.2)
  invFun q := (q.1.1, q.2)
  source := {z | 0 < z.1 0}
  target := {q | 0 < q.1.1 0}
  map_source' := by
    intro z hz
    change 0 < ((𝓡∂ (d + 1)).symm z.1).1 0
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hz)]
    exact hz
  map_target' := by
    intro q hq
    exact hq
  left_inv' := by
    intro z hz
    change (((𝓡∂ (d + 1)).symm z.1).1, z.2) = z
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hz)]
  right_inv' := by
    intro q _
    change ((𝓡∂ (d + 1)).symm q.1.1, q.2) = q
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le q.1.2]
    rfl
  open_source := isOpen_lt continuous_const
    ((PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℝ) 0).comp continuous_fst)
  open_target := isOpen_lt continuous_const
    ((PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℝ) 0).comp
      (continuous_subtype_val.comp continuous_fst))
  contMDiffOn_toFun := by
    refine ContMDiffOn.prodMk ?_ contDiff_snd.contMDiff.contMDiffOn
    refine ((𝓡∂ (d + 1)).contMDiffOn_symm).comp contDiff_fst.contMDiff.contMDiffOn
      (fun z hz => ?_)
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact le_of_lt (show (0 : ℝ) < z.1 0 from hz)
  contMDiffOn_invFun :=
    (ContMDiff.prodMk_space ((𝓡∂ (d + 1)).contMDiff.comp contMDiff_fst) contMDiff_snd).contMDiffOn

variable {G}

theorem sliceHalfSpaceProd_apply_fst_val {z : EuclideanSpace ℝ (Fin (d + 1)) × G}
    (hz : z ∈ (sliceHalfSpaceProd (d := d) G).source) :
    (sliceHalfSpaceProd (d := d) G z).1.1 = z.1 := by
  change ((𝓡∂ (d + 1)).symm z.1).1 = z.1
  rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt (show (0 : ℝ) < z.1 0 from hz))]

theorem sliceHalfSpaceProd_apply_snd (z : EuclideanSpace ℝ (Fin (d + 1)) × G) :
    (sliceHalfSpaceProd (d := d) G z).2 = z.2 := rfl

variable {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]

/-- Submersion coordinates at an interior point of a manifold (possibly with boundary). -/
theorem exists_interior_submersion_coordinates [FiniteDimensional ℝ E'] [IsManifold I ∞ M]
    {Q' : Type*} [NormedAddCommGroup Q'] [NormedSpace ℝ Q'] [FiniteDimensional ℝ Q']
    {Q : M → Q'} (hQ : ContMDiff I 𝓘(ℝ, Q') ∞ Q) {x : M} (hx : I.IsInteriorPoint x)
    (hsurj : Surjective (mfderiv I 𝓘(ℝ, Q') Q x)) :
    ∃ θ : PartialDiffeomorph I
        𝓘(ℝ, Q' × (Fin (Module.finrank ℝ E' - Module.finrank ℝ Q') → ℝ)) M
        (Q' × (Fin (Module.finrank ℝ E' - Module.finrank ℝ Q') → ℝ)) ∞,
      x ∈ θ.source ∧ (∀ y ∈ θ.source, (θ y).1 = Q y) ∧ (θ x).2 = 0 := by
  let ψ := DifferentialGeometry.Manifold.interiorChart I ∞ x
  have hxψ : x ∈ ψ.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  let g : E' → Q' := Q ∘ ψ.symm
  have hgM : ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, Q') ∞ g ψ.target :=
    hQ.comp_contMDiffOn ψ.symm.contMDiffOn
  have hg : ContDiffOn ℝ ∞ g ψ.target := contMDiffOn_iff_contDiffOn.mp hgM
  have hsurj' : Surjective (fderiv ℝ g (ψ x)) := by
    have hgd : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, Q') g (ψ x) :=
      (hgM.contMDiffAt (ψ.open_target.mem_nhds (ψ.map_source hxψ))).mdifferentiableAt (by simp)
    have hψd : MDifferentiableAt I 𝓘(ℝ, E') ψ x := ψ.mdifferentiableAt (by simp) hxψ
    have heq : g ∘ ψ =ᶠ[𝓝 x] Q :=
      Filter.eventuallyEq_of_mem (ψ.open_source.mem_nhds hxψ)
        (fun y hy => congrArg Q (ψ.left_inv hy))
    have hh := mfderiv_comp x hgd hψd
    intro w
    obtain ⟨v, hv⟩ := hsurj w
    refine ⟨mfderiv I 𝓘(ℝ, E') ψ x v, ?_⟩
    have h1 : mfderiv I 𝓘(ℝ, Q') (g ∘ ψ) x v = w := by
      rw [heq.mfderiv_eq]
      exact hv
    rw [hh, mfderiv_eq_fderiv] at h1
    exact h1
  obtain ⟨Θ, hxΘ, -, hΘ, hΘ0⟩ := RegularZero.exists_coordinates_finrank (n := ∞) (by simp)
    ψ.open_target hg (ψ.map_source hxψ) hsurj'
  refine ⟨ψ.trans Θ, ⟨hxψ, hxΘ⟩, fun y hy => ?_, hΘ0⟩
  change (Θ (ψ y)).1 = Q y
  rw [hΘ]
  exact congrArg Q (ψ.left_inv hy.1)

theorem sliceHalfSpaceProd_trans_spec {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (θ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)) × G) M
      (EuclideanSpace ℝ (Fin (d + 1)) × G) ∞)
    {y : M} (hy : y ∈ (θ.trans (sliceHalfSpaceProd G)).source) :
    ((θ.trans (sliceHalfSpaceProd G)) y).1.1 = (θ y).1 ∧
      ((θ.trans (sliceHalfSpaceProd G)) y).2 = (θ y).2 :=
  ⟨sliceHalfSpaceProd_apply_fst_val hy.2, rfl⟩

/-- Interior slice chart (height `0`): `Ψ x = 0`, `dΨ x` onto and `0 < B x`, at an interior
point of the ambient manifold. -/
theorem exists_sliceChart_of_pos [FiniteDimensional ℝ E'] [IsManifold I ∞ M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (hdim : Module.finrank ℝ E' = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff I 𝓘(ℝ, G) ∞ Ψ) {B : M → ℝ} (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    {x : M} (hx : I.IsInteriorPoint x) (hBx : 0 < B x)
    (hreg : Surjective (mfderiv I 𝓘(ℝ, G) Ψ x)) :
    ∃ Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G)) M
        (EuclideanHalfSpace (d + 1) × G) ∞,
      x ∈ Φ.source ∧ (∀ y ∈ Φ.source, 0 < (Φ y).1.1 0) ∧
      ∀ y ∈ Φ.source, ((Ψ y = 0 ∧ 0 ≤ B y) ↔ ((Φ y).2 = 0 ∧ 0 ≤ (Φ y).1.1 0)) := by
  obtain ⟨θ, hxθ, hθ, hθ0⟩ := exists_interior_submersion_coordinates hΨ hx hreg
  have hjd : Module.finrank ℝ (Fin (Module.finrank ℝ E' - Module.finrank ℝ G) → ℝ) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) := by
    rw [Module.finrank_fin_fun, finrank_euclideanSpace_fin]
    omega
  let L : (Fin (Module.finrank ℝ E' - Module.finrank ℝ G) → ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (d + 1)) := ContinuousLinearEquiv.ofFinrankEq hjd
  let A : (G × (Fin (Module.finrank ℝ E' - Module.finrank ℝ G) → ℝ)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin (d + 1)) × G) :=
    (ContinuousLinearEquiv.prodComm ℝ G _).trans (L.prodCongr (ContinuousLinearEquiv.refl ℝ G))
  let θ' := θ.trans (sliceAffine A ((EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (d + 1))),
    (0 : G))).toPartialDiffeomorph
  have hθ'1 : ∀ y, (θ' y).1 = L (θ y).2 + EuclideanSpace.single 0 1 := fun y => rfl
  have hθ'2 : ∀ y, (θ' y).2 = (θ y).1 := fun y => add_zero _
  let Φ₀ := θ'.trans (sliceHalfSpaceProd G)
  have hU : IsOpen (Φ₀.source ∩ B ⁻¹' Ioi 0) :=
    Φ₀.open_source.inter (isOpen_Ioi.preimage hB.continuous)
  let Φ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ₀ _ hU
  have hspec : ∀ y ∈ Φ.source, (Φ y).1.1 = (θ' y).1 ∧ (Φ y).2 = (θ' y).2 :=
    fun y hy => sliceHalfSpaceProd_trans_spec θ' hy.1
  have hpos : ∀ y ∈ Φ.source, 0 < (Φ y).1.1 0 := by
    intro y hy
    rw [(hspec y hy).1]
    exact hy.1.2
  refine ⟨Φ, ?_, hpos, ?_⟩
  · have hx1 : 0 < (θ' x).1 0 := by
      rw [hθ'1, hθ0, map_zero, zero_add]
      simp
    have hΦ₀ : x ∈ Φ₀.source := ⟨⟨hxθ, mem_univ _⟩, hx1⟩
    exact ⟨hΦ₀, hΦ₀, hBx⟩
  · intro y hy
    have hyθ : y ∈ θ.source := hy.1.1.1
    have hBy : 0 < B y := hy.2.2
    rw [(hspec y hy).2, hθ'2, hθ y hyθ]
    exact ⟨fun h => ⟨h.1, (hpos y hy).le⟩, fun h => ⟨h.1, hBy.le⟩⟩

/-- Boundary slice chart (height `1`): `Ψ x = 0`, `B x = 0`, `d(Ψ, B) x` onto, at an interior
point of the ambient manifold. -/
theorem exists_sliceChart_of_zero [FiniteDimensional ℝ E'] [IsManifold I ∞ M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (hdim : Module.finrank ℝ E' = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff I 𝓘(ℝ, G) ∞ Ψ) {B : M → ℝ} (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    {x : M} (hx : I.IsInteriorPoint x) (hBx : B x = 0)
    (hreg : Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x)) :
    ∃ Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G)) M
        (EuclideanHalfSpace (d + 1) × G) ∞,
      x ∈ Φ.source ∧ (Φ x).1.1 0 = 1 ∧
      ∀ y ∈ Φ.source, ((Ψ y = 0 ∧ 0 ≤ B y) ↔ ((Φ y).2 = 0 ∧ 1 ≤ (Φ y).1.1 0)) := by
  obtain ⟨θ, hxθ, hθ, hθ0⟩ := exists_interior_submersion_coordinates (hΨ.prodMk_space hB) hx hreg
  have hjd : Module.finrank ℝ (Fin (Module.finrank ℝ E' - Module.finrank ℝ (G × ℝ)) → ℝ) =
      Module.finrank ℝ (Fin d → ℝ) := by
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_self]
    omega
  let L : (Fin (Module.finrank ℝ E' - Module.finrank ℝ (G × ℝ)) → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq hjd
  let C : (ℝ × (Fin d → ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
    (Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)).trans (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm
  have hC : ∀ b v, C (b, v) 0 = b := fun b v => by simp [C]
  let A : ((G × ℝ) × (Fin (Module.finrank ℝ E' - Module.finrank ℝ (G × ℝ)) → ℝ)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin (d + 1)) × G) :=
    ((ContinuousLinearEquiv.prodAssoc ℝ G ℝ _).trans (ContinuousLinearEquiv.prodComm ℝ G _)).trans
      ((((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr L).trans C).prodCongr
        (ContinuousLinearEquiv.refl ℝ G))
  let θ' := θ.trans (sliceAffine A ((EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (d + 1))),
    (0 : G))).toPartialDiffeomorph
  have hθ'1 : ∀ y, (θ' y).1 0 = (θ y).1.2 + 1 := by
    intro y
    change (C ((θ y).1.2, L (θ y).2) + EuclideanSpace.single 0 1 :
      EuclideanSpace ℝ (Fin (d + 1))) 0 = _
    rw [PiLp.add_apply, hC]
    simp
  have hθ'2 : ∀ y, (θ' y).2 = (θ y).1.1 := fun y => add_zero _
  let Φ := θ'.trans (sliceHalfSpaceProd G)
  have hx1 : 0 < (θ' x).1 0 := by
    rw [hθ'1, hθ x hxθ, hBx]
    norm_num
  have hxΦ : x ∈ Φ.source := ⟨⟨hxθ, mem_univ _⟩, hx1⟩
  refine ⟨Φ, hxΦ, ?_, ?_⟩
  · rw [(sliceHalfSpaceProd_trans_spec θ' hxΦ).1, hθ'1, hθ x hxθ, hBx, zero_add]
  · intro y hy
    have hyθ : y ∈ θ.source := hy.1.1
    rw [(sliceHalfSpaceProd_trans_spec θ' hy).1, (sliceHalfSpaceProd_trans_spec θ' hy).2,
      hθ'1, hθ'2, hθ y hyθ]
    constructor
    · intro h
      exact ⟨h.1, by linarith [h.2]⟩
    · intro h
      exact ⟨h.1, by linarith [h.2]⟩

end Producers

section AmbientBoundary

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]

/-- `ℍ ≅ ℍ × ℝ⁰`. -/
def sliceZeroProd (m : ℕ) :
    Diffeomorph (𝓡∂ (m + 1)) ((𝓡∂ (m + 1)).prod 𝓘(ℝ, Fin 0 → ℝ)) (EuclideanHalfSpace (m + 1))
      (EuclideanHalfSpace (m + 1) × (Fin 0 → ℝ)) ∞ where
  toFun w := (w, 0)
  invFun q := q.1
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  contMDiff_toFun := contMDiff_id.prodMk contMDiff_const
  contMDiff_invFun := contMDiff_fst

/-- Restricted ambient chart (ambient model `𝓡∂`), codimension zero, height `0`. -/
theorem exists_sliceChart_restrict [IsManifold (𝓡∂ (m + 1)) ∞ M] (x : M) {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ Φ : PartialDiffeomorph (𝓡∂ (m + 1)) ((𝓡∂ (m + 1)).prod 𝓘(ℝ, Fin 0 → ℝ)) M
        (EuclideanHalfSpace (m + 1) × (Fin 0 → ℝ)) ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧
      ((Φ x).1.1 0 = 0 ↔ (𝓡∂ (m + 1)).IsBoundaryPoint x) := by
  let c : PartialDiffeomorph (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) M (EuclideanHalfSpace (m + 1)) ∞ :=
    { toPartialEquiv := (chartAt (EuclideanHalfSpace (m + 1)) x).toPartialEquiv
      open_source := (chartAt (EuclideanHalfSpace (m + 1)) x).open_source
      open_target := (chartAt (EuclideanHalfSpace (m + 1)) x).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  let Φ := (DifferentialGeometry.Topology.PartialDiffeomorph.restrict c U hU).trans
    (sliceZeroProd m).toPartialDiffeomorph
  refine ⟨Φ, ⟨⟨mem_chart_source _ x, hxU⟩, mem_univ _⟩, fun y hy => hy.1.2, ?_⟩
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace]
  exact eq_comm

end AmbientBoundary

end DifferentialGeometry.Manifold.RegularLevel
