import DifferentialGeometry.Geometry.Thurston.FoldDescent

/-!
# The local composite relation of a fold

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§3, after review 21: the same-image normal form of a fold is a relation closed under inverse and
composition, not a list of generators). For a metric `g` on `X`, an open `N` and a map `F : X → M`
(read on `N`), `FoldRel g N F y y'` holds when an isometry `γ` of `g` carries `y` to `y'` and
preserves `F` on an open neighbourhood `U ⊆ N` of `y` with `γ U ⊆ N`: exactly the hypothesis of
`metricFiberCompatible_of_foldPairs`. It is reflexive on `N`, symmetric and transitive
(`FoldRel.refl`, `FoldRel.symm`, `FoldRel.trans`), and if every pair of points of `N` with the same
image is related, the restricted metric is compatible with the fold
(`metricFiberCompatible_of_foldRel`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff Topology

namespace GC.Geometry

variable {E H X M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]

def FoldRel (g : SmoothRiemannianMetric I X) (N : Set X) (F : X → M) (y y' : X) : Prop :=
  ∃ γ : X ≃ₘ⟮I, I⟯ X, Diffeomorph.pullbackMetric g γ = g ∧ γ y = y' ∧
    ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ U ⊆ N ∧ Set.MapsTo γ U N ∧ ∀ z ∈ U, F (γ z) = F z

namespace FoldRel

variable {g : SmoothRiemannianMetric I X} {N : Set X} {F : X → M}

theorem refl (hN : IsOpen N) {y : X} (hy : y ∈ N) : FoldRel g N F y y :=
  ⟨Diffeomorph.refl I X ∞, Diffeomorph.pullbackMetric_refl g, rfl, N, hN, hy, subset_rfl,
    fun _ hz => hz, fun _ _ => rfl⟩

theorem isometry_symm {γ : X ≃ₘ⟮I, I⟯ X} (hγ : Diffeomorph.pullbackMetric g γ = g) :
    Diffeomorph.pullbackMetric g γ.symm = g := by
  conv_lhs => rw [← hγ]
  rw [Diffeomorph.pullbackMetric_trans]
  have h : γ.symm.trans γ = Diffeomorph.refl I X ∞ := by
    ext x
    exact γ.apply_symm_apply x
  rw [h, Diffeomorph.pullbackMetric_refl]

theorem isometry_trans {γ γ' : X ≃ₘ⟮I, I⟯ X} (hγ : Diffeomorph.pullbackMetric g γ = g)
    (hγ' : Diffeomorph.pullbackMetric g γ' = g) :
    Diffeomorph.pullbackMetric g (γ.trans γ') = g := by
  rw [← Diffeomorph.pullbackMetric_trans, hγ', hγ]

theorem symm {y y' : X} (h : FoldRel g N F y y') : FoldRel g N F y' y := by
  obtain ⟨γ, hγ, hyy, U, hU, hyU, hUN, hmaps, hF⟩ := h
  refine ⟨γ.symm, isometry_symm hγ, ?_, γ.symm ⁻¹' U, hU.preimage γ.symm.continuous, ?_, ?_, ?_,
    ?_⟩
  · rw [← hyy, Diffeomorph.symm_apply_apply]
  · change γ.symm y' ∈ U
    rw [← hyy, Diffeomorph.symm_apply_apply]
    exact hyU
  · intro w hw
    have := hmaps hw
    rwa [Diffeomorph.apply_symm_apply] at this
  · intro w hw
    exact hUN hw
  · intro w hw
    have := hF _ hw
    rw [Diffeomorph.apply_symm_apply] at this
    exact this.symm

theorem trans {y y' y'' : X} (h : FoldRel g N F y y') (h' : FoldRel g N F y' y'') :
    FoldRel g N F y y'' := by
  obtain ⟨γ, hγ, hyy, U, hU, hyU, hUN, hmaps, hF⟩ := h
  obtain ⟨γ', hγ', hyy', U', hU', hyU', hUN', hmaps', hF'⟩ := h'
  refine ⟨γ.trans γ', isometry_trans hγ hγ', ?_, U ∩ γ ⁻¹' U',
    hU.inter (hU'.preimage γ.continuous), ⟨hyU, ?_⟩, fun z hz => hUN hz.1, ?_, ?_⟩
  · change γ' (γ y) = y''
    rw [hyy, hyy']
  · change γ y ∈ U'
    rw [hyy]
    exact hyU'
  · intro z hz
    exact hmaps' hz.2
  · intro z hz
    change F (γ' (γ z)) = F z
    rw [hF' _ hz.2, hF _ hz.1]

theorem of_eq {y y' : X} (hN : IsOpen N) (hy : y ∈ N) (h : y = y') : FoldRel g N F y y' :=
  h ▸ refl hN hy

theorem mem_left {y y' : X} (h : FoldRel g N F y y') : y ∈ N := by
  obtain ⟨_, _, _, U, _, hyU, hUN, _⟩ := h
  exact hUN hyU

theorem mem_right {y y' : X} (h : FoldRel g N F y y') : y' ∈ N :=
  h.symm.mem_left

theorem map_eq {y y' : X} (h : FoldRel g N F y y') : F y' = F y := by
  obtain ⟨γ, _, hyy, U, _, hyU, _, _, hF⟩ := h
  rw [← hyy]
  exact hF y hyU

end FoldRel

theorem metricFiberCompatible_of_foldRel [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] (g : SmoothRiemannianMetric I X)
    (N : TopologicalSpace.Opens X) (F : X → M)
    (hF : IsLocalDiffeomorph I I ∞ (fun p : N => F p))
    (hrel : ∀ y y' : X, y ∈ N → y' ∈ N → F y = F y' → FoldRel g N F y y') :
    metricFiberCompatible (g.restrictOpen N) (fun p : N => F p) hF := by
  refine metricFiberCompatible_of_foldPairs g N _ hF fun y y' hyy => ?_
  obtain ⟨γ, hγ, hyy', U, hU, hyU, hUN, hmaps, hFU⟩ := hrel y y' y.2 y'.2 hyy
  exact ⟨γ, hγ, hyy', ⟨U, hU⟩, hyU, hUN, hmaps, fun z => hFU z z.2⟩

end GC.Geometry
