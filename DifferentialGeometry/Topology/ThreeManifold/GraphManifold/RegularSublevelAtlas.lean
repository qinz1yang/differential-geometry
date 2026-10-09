import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Orientation
import DifferentialGeometry.Topology.Manifold.RegularLevel.Coordinates
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

/-!
# Regular sublevel sets as smooth boundary atlases

For a smooth function `f` on a boundaryless manifold whose differential does not vanish on the
level `f = a`, the sublevel set `{f ≤ a}` carries a `SmoothBoundaryAtlas` whose boundary points
are exactly the points of the level set. We also pull back a manifold orientation along any
smooth map with bijective differentials.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SmoothBoundaryAtlas

def firstCoordinateEquiv (m : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin m) ℝ)).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (m + 1) => ℝ)).trans
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm)

theorem firstCoordinateEquiv_apply_zero (m : ℕ) (v : ℝ × EuclideanSpace ℝ (Fin m)) :
    firstCoordinateEquiv m v 0 = v.1 := rfl

def affineDiffeomorph {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (c : F) : E ≃ₘ[ℝ] F where
  toFun v := L v + c
  invFun w := L.symm (w - c)
  left_inv v := by simp
  right_inv w := by simp
  contMDiff_toFun := (L.contDiff.add contDiff_const).contMDiff
  contMDiff_invFun := (L.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff

theorem affineDiffeomorph_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (c : F) (v : E) :
    affineDiffeomorph L c v = L v + c := rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_partialDiffeomorph_coord_eq_sub {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hreg : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) (a : ℝ) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) M
        (EuclideanSpace ℝ (Fin (n + 1))) ∞,
      x ∈ φ.source ∧ ∀ y ∈ φ.source, φ y 0 = a - f y := by
  have hneg : mfderiv I 𝓘(ℝ, ℝ) (-f) x ≠ 0 := by
    rw [mfderiv_neg]
    exact neg_ne_zero.mpr hreg
  have hcoord : ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) M
      (ℝ × EuclideanSpace ℝ (Fin n)) ∞, x ∈ Φ.source ∧ ∀ y ∈ Φ.source, (Φ y).1 = (-f) y := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    obtain ⟨Φ, hx, -, hΦ⟩ := Manifold.RegularLevel.exists_product_coordinates_of_contMDiffOn
      (m := n) I hdim isOpen_univ hf.neg.contMDiffOn (mem_univ x) hneg
    exact ⟨Φ, hx, hΦ⟩
  obtain ⟨Φ, hx, hΦ⟩ := hcoord
  let D := affineDiffeomorph (firstCoordinateEquiv n) (a • EuclideanSpace.single 0 1)
  refine ⟨Φ.trans D.toPartialDiffeomorph, ⟨hx, mem_univ _⟩, fun y hy => ?_⟩
  change (firstCoordinateEquiv n (Φ y) + a • EuclideanSpace.single 0 1 :
    EuclideanSpace ℝ (Fin (n + 1))) 0 = a - f y
  rw [PiLp.add_apply, firstCoordinateEquiv_apply_zero, hΦ y hy.1]
  simp [sub_eq_neg_add]

theorem exists_partialDiffeomorph_coord_pos {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    {s : Set M} (hs : IsOpen s) {x : M} (hx : x ∈ s) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) M
        (EuclideanSpace ℝ (Fin (n + 1))) ∞,
      x ∈ φ.source ∧ φ.source ⊆ s ∧ ∀ y ∈ φ.source, 0 < φ y 0 := by
  let c := DifferentialGeometry.Topology.PartialDiffeomorph.extendedChart (I := I) x
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (hdim.trans finrank_euclideanSpace_fin.symm)
  let D := affineDiffeomorph L ((1 - L (c x) 0) • EuclideanSpace.single 0 1)
  let ψ := c.trans D.toPartialDiffeomorph
  have hψx : ψ x 0 = 1 := by
    change (L (c x) + (1 - L (c x) 0) • EuclideanSpace.single 0 1 :
      EuclideanSpace ℝ (Fin (n + 1))) 0 = 1
    simp
  have hxψ : x ∈ ψ.source := ⟨mem_extChartAt_source (I := I) x, mem_univ _⟩
  let U := (ψ.source ∩ ψ ⁻¹' {v : EuclideanSpace ℝ (Fin (n + 1)) | 0 < v 0}) ∩ s
  have hU : IsOpen U :=
    (ψ.contMDiffOn.continuousOn.isOpen_inter_preimage ψ.open_source
      (isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous))).inter hs
  let φ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict ψ U hU
  refine ⟨φ, ⟨hxψ, ⟨hxψ, by simp [hψx]⟩, hx⟩, fun y hy => hy.2.2, fun y hy => hy.2.1.2⟩

theorem exists_sublevel_chart {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {x : M} (hx : f x ≤ a) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) M
        (EuclideanSpace ℝ (Fin (n + 1))) ∞,
      x ∈ φ.source ∧ (∀ y ∈ φ.source, (f y ≤ a ↔ 0 ≤ φ y 0)) ∧ (φ x 0 = 0 ↔ f x = a) := by
  by_cases hxa : f x = a
  · obtain ⟨φ, hφx, hφ⟩ := exists_partialDiffeomorph_coord_eq_sub I hdim hf (hreg x hxa) a
    refine ⟨φ, hφx, fun y hy => ?_, ?_⟩
    · rw [hφ y hy, sub_nonneg]
    · rw [hφ x hφx, sub_eq_zero, eq_comm]
  · have hlt : f x < a := lt_of_le_of_ne hx hxa
    obtain ⟨φ, hφx, hsub, hpos⟩ := exists_partialDiffeomorph_coord_pos I hdim
      (isOpen_lt hf.continuous continuous_const) hlt
    refine ⟨φ, hφx, fun y hy => ?_, ?_⟩
    · exact iff_of_true (hsub hy).le (hpos y hy).le
    · exact iff_of_false (hpos x hφx).ne' hxa

def regularSublevel {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (a : ℝ)
    (hreg : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    SmoothBoundaryAtlas I (n + 1) {x | f x ≤ a} where
  ambientChart x := Classical.choose (exists_sublevel_chart I hdim hf hreg x.2)
  mem_source x := (Classical.choose_spec (exists_sublevel_chart I hdim hf hreg x.2)).1
  mem_iff x := (Classical.choose_spec (exists_sublevel_chart I hdim hf hreg x.2)).2.1

theorem regularSublevel_ambientChart_eq_zero_iff {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (a : ℝ)
    (hreg : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) (x : {x | f x ≤ a}) :
    (regularSublevel I hdim hf a hreg).ambientChart x x.val 0 = 0 ↔ f x = a :=
  (Classical.choose_spec (exists_sublevel_chart I hdim hf hreg x.2)).2.2

theorem regularSublevel_isBoundaryPoint_iff {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (a : ℝ)
    (hreg : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) (x : {x | f x ≤ a}) :
    letI := (regularSublevel I hdim hf a hreg).toChartedSpace
    (𝓡∂ (n + 1)).IsBoundaryPoint x ↔ f x = a := by
  rw [(regularSublevel I hdim hf a hreg).isBoundaryPoint_iff]
  exact regularSublevel_ambientChart_eq_zero_iff I hdim hf a hreg x

theorem regularSublevel_isInteriorPoint_iff {n : ℕ} (hdim : Module.finrank ℝ E = n + 1)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (a : ℝ)
    (hreg : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) (x : {x | f x ≤ a}) :
    letI := (regularSublevel I hdim hf a hreg).toChartedSpace
    (𝓡∂ (n + 1)).IsInteriorPoint x ↔ f x < a := by
  let := (regularSublevel I hdim hf a hreg).toChartedSpace
  rw [← not_iff_not, ← ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    regularSublevel_isBoundaryPoint_iff I hdim hf a hreg x, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm x.2 h⟩

end DifferentialGeometry.Topology.SmoothBoundaryAtlas

namespace DifferentialGeometry.Topology.Manifold

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] (J : ModelWithCorners ℝ F K)
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem orientation_cast_apply_eq_reindex {a b : ℕ} (h : a = b)
    (O : ManifoldOrientation I M a) (x : M) :
    (cast (congrArg (fun k => ManifoldOrientation I M k) h) O).orientation x =
      Orientation.reindex ℝ (TangentSpace I x) (finCongr h) (O.orientation x) := by
  subst b
  change O.orientation x = Orientation.reindex ℝ (TangentSpace I x) (Equiv.refl _) _
  rw [Orientation.reindex_refl]
  rfl

theorem exists_manifoldOrientation_pullback {n : ℕ} (hn : Module.finrank ℝ E = n)
    (f : M → N) (hf : ContMDiff I J ∞ f) (hbij : ∀ x, Bijective (mfderiv I J f x))
    (O : ManifoldOrientation J N n) :
    ∃ OM : ManifoldOrientation I M n, ∀ x : M,
      Orientation.map (Fin n) (differentialEquivOfBijective I J f hbij x).toLinearEquiv
        (OM.orientation x) = O.orientation (f x) := by
  have hF := O.dimension_eq
  let O' : ManifoldOrientation J N (Module.finrank ℝ F) :=
    cast (congrArg (fun k => ManifoldOrientation J N k) hF.symm) O
  have hO' (y : N) : O'.orientation y =
      Orientation.reindex ℝ (TangentSpace J y) (finCongr hF.symm) (O.orientation y) :=
    orientation_cast_apply_eq_reindex J hF.symm O y
  let s := smoothOrientationOfManifoldOrientation J O'
  let t := pullbackSmoothOrientation I J f hf hbij s
  obtain ⟨OM, hOM⟩ := exists_manifoldOrientation_eq_of_smoothOrientation I t
  let OM' : ManifoldOrientation I M n :=
    cast (congrArg (fun k => ManifoldOrientation I M k) hn) OM
  have hOM' (x : M) : OM'.orientation x =
      Orientation.reindex ℝ (TangentSpace I x) (finCongr hn) (t.val x) := by
    rw [show OM'.orientation x = _ from orientation_cast_apply_eq_reindex I hn OM x]
    rw [congrFun hOM x]
  refine ⟨OM', ?_⟩
  intro x
  rw [hOM']
  change Orientation.map (Fin n) (differentialEquivOfBijective I J f hbij x).toLinearEquiv
    (Orientation.reindex ℝ E (finCongr hn)
      (tangentOrientationEquiv (differentialEquivOfBijective I J f hbij x).symm.toLinearEquiv
        (O'.orientation (f x)))) = _
  rw [hO']
  exact tangentOrientationEquiv_symm_reindex_map
    (differentialEquivOfBijective I J f hbij x).toLinearEquiv hn hF (O.orientation (f x))

def manifoldOrientationPullback {n : ℕ} (hn : Module.finrank ℝ E = n)
    (f : M → N) (hf : ContMDiff I J ∞ f) (hbij : ∀ x, Bijective (mfderiv I J f x))
    (O : ManifoldOrientation J N n) : ManifoldOrientation I M n :=
  Classical.choose (exists_manifoldOrientation_pullback I J hn f hf hbij O)

theorem orientation_map_manifoldOrientationPullback {n : ℕ} (hn : Module.finrank ℝ E = n)
    (f : M → N) (hf : ContMDiff I J ∞ f) (hbij : ∀ x, Bijective (mfderiv I J f x))
    (O : ManifoldOrientation J N n) (x : M) :
    Orientation.map (Fin n) (differentialEquivOfBijective I J f hbij x).toLinearEquiv
      ((manifoldOrientationPullback I J hn f hf hbij O).orientation x) = O.orientation (f x) :=
  Classical.choose_spec (exists_manifoldOrientation_pullback I J hn f hf hbij O) x

end DifferentialGeometry.Topology.Manifold
