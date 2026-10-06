import DifferentialGeometry.Topology.Manifold.ImmersionBoundaryOpenHCOL
import DifferentialGeometry.Topology.Manifold.ImmersionPartialDiffeomorphHCOL
import DifferentialGeometry.Topology.Ehresmann.Interval
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
# The smooth half-collar of a boundary-torus embedding (lane S-COLLAR, G1, suffix `_HCOL`)

`BoundaryTori.collar` (and with it the `CuspCores` fields `external_end`, `collar_owned`,
`collar_closure_off`) needs a `PartialDiffeomorph halfCollarModel W.model
(Torus × EuclideanHalfSpace 1) W.Carrier ∞` with source `{s < 1}`.  The labelled product of BCG06 /
E4c gives only a smooth embedding `Φ : T² × [0, 1] → W` (an equal-dimension embedding whose end `0`
lies on `∂W`).

* `iccLeftPartialDiffeomorph_HCOL`: the left chart of `[a, b]` as a `PartialDiffeomorph` onto
  `{s < b - a} ⊆ H¹`;
* `halfCollar_of_boundary_embedding_general_HCOL` (model-generic) and
  **`halfCollar_of_boundary_embedding_HCOL`** (`W : CompactCarrier`): `Φ` smooth embedding,
  `Φ (t, 0) ∈ ∂W` ⟹ a `PartialDiffeomorph` `d` on `Torus × H¹` with source `halfCollarSource`,
  target `Φ '' {p₂ < 1/2}` (open image) and `d (t, s) = Φ (t, s / 2)`; smooth inverse, no flow.
  Proof: the inverse function theorem with boundary
  (`IsImmersionAt.nhds_le_map_of_halfSpace_HCOL` and
  `exists_partialDiffeomorph_of_open_injOn_immersion_HCOL`) on `T² × [0, 2]` for
  `Φ ∘ (t, z ↦ (t, z / 2))` restricted to `{z < 1}`, precomposed with the inverse of the left
  chart of `[0, 2]`;
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff
open Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold.Assembly
open DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Topology.HalfCollarHCOL

universe u

/-- The left chart of `[a, b]` as a `C^∞` partial diffeomorphism onto `{s < b - a} ⊆ H¹`. -/
def iccLeftPartialDiffeomorph_HCOL (a b : ℝ) [Fact (a < b)] :
    PartialDiffeomorph (𝓡∂ 1) (𝓡∂ 1) (Icc a b) (EuclideanHalfSpace 1) ∞ where
  toPartialEquiv := (IccLeftChart a b).toPartialEquiv
  open_source := (IccLeftChart a b).open_source
  open_target := (IccLeftChart a b).open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (Set.mem_insert _ _))
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (Set.mem_insert _ _))

/-- The range of the carrier model is `univ` or a closed half-space. -/
theorem range_carrierModel_HCOL (k : CarrierModel) :
    range k.model = univ ∨ ∃ ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, ℓ ≠ 0 ∧
      range k.model = {w | 0 ≤ ℓ w} := by
  cases k with
  | closed => exact Or.inl (ModelWithCorners.Boundaryless.range_eq_univ (I := 𝓡 3))
  | withBoundary =>
    refine Or.inr ⟨EuclideanSpace.proj 0, fun h => ?_, ?_⟩
    · have := congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ =>
        L (EuclideanSpace.single 0 1)) h
      simp at this
    · change range (𝓡∂ 3) = _
      rw [range_modelWithCornersEuclideanHalfSpace]
      rfl

/-- The range of the half-collar model is the closed half-space `{v | 0 ≤ v.2 0}`. -/
theorem range_halfCollarModel_HCOL :
    range (torusModel.prod (𝓡∂ 1)) =
      {v | 0 ≤ ((EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))) v} := by
  rw [ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace]
  ext v
  simp [torusModel]

/-- **The smooth half-collar of a boundary-torus embedding (model-generic form).**
`Φ : T² × [0, 1] → N` a smooth embedding into a manifold modelled on `J` (range `univ` or a closed
half-space, dimension `3`) with `Φ (·, 0)` on `∂N`: there is a `C^∞` partial diffeomorphism `d` of
`T² × H¹` onto the open set `Φ '' {p₂ < 1/2}` with source `{s < 1}` (`halfCollarSource`) and
`d (t, s) = Φ (t, s/2)`. -/
theorem halfCollar_of_boundary_embedding_general_HCOL {E'' : Type u} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [FiniteDimensional ℝ E''] {G : Type*} [TopologicalSpace G]
    {J : ModelWithCorners ℝ E'' G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N]
    (hdim : Module.finrank ℝ ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ E'')
    (hJ : range J = univ ∨ ∃ ℓ₂ : E'' →L[ℝ] ℝ, ℓ₂ ≠ 0 ∧ range J = {w | 0 ≤ ℓ₂ w})
    (Φ : Torus × Icc (0 : ℝ) 1 → N)
    (hΦ : IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) J ∞ Φ)
    (h0 : ∀ t, J.IsBoundaryPoint (Φ (t, iccEnd false))) :
    ∃ d : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞,
      d.source = halfCollarSource ∧ d.target = Φ '' {p | (p.2 : ℝ) < 1 / 2} ∧
      ∀ (t : Torus) (s : EuclideanHalfSpace 1) (z : Icc (0 : ℝ) 1),
        s.val 0 < 1 → (z : ℝ) = s.val 0 / 2 → d (t, s) = Φ (t, z) := by
  have : Fact ((0 : ℝ) < 2) := ⟨two_pos⟩
  let R : Diffeomorph (torusModel.prod (𝓡∂ 1)) (torusModel.prod (𝓡∂ 1))
      (Torus × Icc (0 : ℝ) 2) (Torus × Icc (0 : ℝ) 1) ∞ :=
    (Diffeomorph.refl torusModel Torus ∞).prodCongr (affineIntervalDiffeomorph 0 2).symm
  have hR : ∀ p, ((R p).2 : ℝ) = (p.2 : ℝ) / 2 := fun p => by
    change (((affineIntervalDiffeomorph 0 2).symm p.2 : Icc (0 : ℝ) 1) : ℝ) = _
    rw [affineIntervalDiffeomorph_symm_apply]
    norm_num
  have hR1 : ∀ p, (R p).1 = p.1 := fun p => rfl
  let Ψ : Torus × Icc (0 : ℝ) 2 → N := Φ ∘ R
  have hΨ : IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) J ∞ Ψ := hΦ.comp_diffeomorph R
  let S₀ : Set (Torus × Icc (0 : ℝ) 2) := {p | (p.2 : ℝ) < 1}
  have hS₀o : IsOpen S₀ := isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
  have hne : Nonempty (Torus × Icc (0 : ℝ) 2) := ⟨((1, 1), ⟨0, le_rfl, two_pos.le⟩)⟩
  have hI : ∃ ℓ₁ : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ, ℓ₁ ≠ 0 ∧
      range (torusModel.prod (𝓡∂ 1)) = {v | 0 ≤ ℓ₁ v} := by
    refine ⟨(EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))),
      fun h => ?_, range_halfCollarModel_HCOL⟩
    have := congrArg (fun L : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ => L ((0, 0), EuclideanSpace.single 0 1)) h
    simp at this
  have hbd : ∀ y ∈ S₀, (torusModel.prod (𝓡∂ 1)).IsBoundaryPoint y →
      J.IsBoundaryPoint (Ψ y) := by
    rintro ⟨t, z⟩ hy hb
    have hmem : (t, z) ∈ (torusModel.prod (𝓡∂ 1)).boundary (Torus × Icc (0 : ℝ) 2) := hb
    rw [ModelWithCorners.boundary_of_boundaryless_left, boundary_Icc] at hmem
    rcases hmem.2 with hz | hz
    · have hR0 : R (t, z) = (t, iccEnd false) := by
        refine Prod.ext rfl (Subtype.ext ?_)
        rw [hR, hz]
        simp [iccEnd]
      change J.IsBoundaryPoint (Φ (R (t, z)))
      rw [hR0]
      exact h0 t
    · exfalso
      have h1 : (((t, z).2 : Icc (0 : ℝ) 2) : ℝ) < 1 := hy
      rw [Set.mem_singleton_iff.mp hz] at h1
      change (2 : ℝ) < 1 at h1
      linarith
  have hopen : ∀ y ∈ S₀, 𝓝 (Ψ y) ≤ Filter.map Ψ (𝓝 y) := fun y hy =>
    (hΨ.isImmersion.isImmersionAt y).nhds_le_map_of_halfSpace_HCOL hdim hI
      hJ (hbd y hy)
  obtain ⟨d₀, hd₀s, hd₀t, hd₀f⟩ := exists_partialDiffeomorph_of_open_injOn_immersion_HCOL
    (I := torusModel.prod (𝓡∂ 1)) (J := J) hS₀o
    (fun y _ => hΨ.isImmersion.isImmersionAt y) hopen hΨ.isEmbedding.injective.injOn
  let Lp := iccLeftPartialDiffeomorph_HCOL 0 2
  let e₂ : PartialDiffeomorph halfCollarModel halfCollarModel (Torus × EuclideanHalfSpace 1)
      (Torus × Icc (0 : ℝ) 2) ∞ :=
    PartialDiffeomorph.prod (Diffeomorph.refl torusModel Torus ∞).toPartialDiffeomorph Lp.symm
  have hLs : ∀ s : EuclideanHalfSpace 1, ((Lp.symm s : Icc (0 : ℝ) 2) : ℝ) = min (s.val 0 + 0) 2 :=
    fun s => by
      have := IccLeftChart_symm_apply (0 : ℝ) 2 s
      exact congrArg (fun z : Icc (0 : ℝ) 2 => (z : ℝ)) this
  have hLt : ∀ s : EuclideanHalfSpace 1, s ∈ Lp.symm.source ↔ s.val 0 < 2 := fun s => by
    change s ∈ (IccLeftChart (0 : ℝ) 2).target ↔ _
    simp [IccLeftChart]
  have hR2 : ∀ (t : Torus) (s : EuclideanHalfSpace 1) (z : Icc (0 : ℝ) 1), s.val 0 < 1 →
      (z : ℝ) = s.val 0 / 2 → R (e₂ (t, s)) = (t, z) := fun t s z hs hz => by
    refine Prod.ext rfl (Subtype.ext ?_)
    rw [hR]
    change ((Lp.symm s : Icc (0 : ℝ) 2) : ℝ) / 2 = _
    rw [hLs, hz, min_eq_left (by linarith)]
    ring
  have hmemT : ∀ w : Torus × Icc (0 : ℝ) 2, w ∈ S₀ → w ∈ e₂.target := fun w hw => by
    have h1 : (w.2 : ℝ) < 1 := hw
    have h2 : (w.2 : ℝ) < 2 := by linarith
    exact ⟨trivial, h2⟩
  refine ⟨e₂.trans d₀, ?_, ?_, ?_⟩
  · ext ⟨t, s⟩
    rw [PartialDiffeomorph.trans_source]
    change ((t, s) ∈ e₂.source ∧ e₂ (t, s) ∈ d₀.source) ↔ s.val 0 < 1
    rw [hd₀s]
    have he : (t, s) ∈ e₂.source ↔ s.val 0 < 2 := by
      change (t ∈ univ ∧ s ∈ Lp.symm.source) ↔ _
      rw [hLt]
      simp
    have hv : (((e₂ (t, s)).2 : Icc (0 : ℝ) 2) : ℝ) = min (s.val 0 + 0) 2 := hLs s
    change (t, s) ∈ e₂.source ∧ (((e₂ (t, s)).2 : Icc (0 : ℝ) 2) : ℝ) < 1 ↔ _
    rw [he, hv]
    constructor
    · rintro ⟨_, h⟩
      rcases min_lt_iff.mp h with h | h <;> linarith
    · intro h
      exact ⟨by linarith, lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩
  · ext y
    change y ∈ d₀.target ∩ d₀.symm ⁻¹' e₂.target ↔ _
    have hy : y ∈ d₀.target ↔ y ∈ Ψ '' S₀ := by rw [hd₀t]
    constructor
    · rintro ⟨hy1, -⟩
      obtain ⟨p, hp, rfl⟩ := hy.mp hy1
      refine ⟨R p, ?_, rfl⟩
      change ((R p).2 : ℝ) < 1 / 2
      rw [hR]
      have : (p.2 : ℝ) < 1 := hp
      linarith
    · rintro ⟨q, hq, rfl⟩
      have hq' : ((q.2 : Icc (0 : ℝ) 1) : ℝ) < 1 / 2 := hq
      have hp : R.symm q ∈ S₀ := by
        have h1 := hR (R.symm q)
        rw [R.apply_symm_apply] at h1
        change ((R.symm q).2 : ℝ) < 1
        linarith
      have hmem : Φ q ∈ d₀.target := by
        rw [hd₀t]
        exact ⟨R.symm q, hp, by simp [Ψ]⟩
      refine ⟨hmem, ?_⟩
      apply hmemT
      rw [← hd₀s]
      exact d₀.map_target hmem
  · intro t s z hs hz
    change d₀ (e₂ (t, s)) = Φ (t, z)
    rw [congrFun hd₀f (e₂ (t, s))]
    change Φ (R (e₂ (t, s))) = _
    rw [hR2 t s z hs hz]


/-- **G1 kernel on a compact carrier.**  `Φ : T² × [0, 1] → W` a smooth embedding with
`Φ (·, 0)` on `∂W`: the `PartialDiffeomorph` shape of `BoundaryTori.collar` (source
`halfCollarSource`), onto the open image `Φ '' {p₂ < 1/2}`, `d (t, s) = Φ (t, s/2)`. -/
theorem halfCollar_of_boundary_embedding_HCOL (W : CompactCarrier.{u})
    (Φ : Torus × Icc (0 : ℝ) 1 → W.Carrier)
    (hΦ : IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ)
    (h0 : ∀ t, W.model.IsBoundaryPoint (Φ (t, iccEnd false))) :
    ∃ d : PartialDiffeomorph halfCollarModel W.model (Torus × EuclideanHalfSpace 1) W.Carrier ∞,
      d.source = halfCollarSource ∧ d.target = Φ '' {p | (p.2 : ℝ) < 1 / 2} ∧
      ∀ (t : Torus) (s : EuclideanHalfSpace 1) (z : Icc (0 : ℝ) 1),
        s.val 0 < 1 → (z : ℝ) = s.val 0 / 2 → d (t, s) = Φ (t, z) :=
  halfCollar_of_boundary_embedding_general_HCOL (J := W.model) (by simp [Module.finrank_prod])
    (range_carrierModel_HCOL W.kind) Φ hΦ h0

end DifferentialGeometry.Topology.HalfCollarHCOL
