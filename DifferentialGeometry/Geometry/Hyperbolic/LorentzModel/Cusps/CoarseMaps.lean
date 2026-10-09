/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Distortion
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.CoarseGeometry.UniformContinuity
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.EquivariantGluing
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.InverseMaps

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.CuspCoarseMaps

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary Busemann
open BoundaryStabilizer CuspTruncation MatchedCusps TranslatedCusps PseudoIsometry

variable {n : ℕ} {hn : 1 ≤ n} {Γ Λ : Subgroup (PO n 1)} {f : Γ ≃* Λ} {r : ℝ}

theorem uniformContinuous_of_cusp_formulas (T : MatchedTruncation hn Γ Λ f r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) {ε : ℝ} (hre : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {Φ : HUpper n → HUpper n} (hc : Continuous Φ) (he : IsFEquivariant f hn Φ)
    (hpiece : ∀ (a : Piece T.source) (x : HUpper n),
      x ∈ pieceSet T.source a → Φ x = pieceMap T a x) : UniformContinuous Φ := by
  classical
  let := poMulAction hn
  let : Finite T.source.centers := T.source.finite_centers
  let := Fintype.ofFinite T.source.centers
  obtain ⟨R, hR⟩ := T.source.compact_core.isBounded.subset_closedBall (basepointH : HUpper n)
  have huc := (isCompact_closedBall (basepointH : HUpper n) (R + 1)).uniformContinuousOn_of_continuous
    hc.continuousOn
  apply Metric.uniformContinuous_iff.mpr
  intro e hepos
  obtain ⟨d₀, hd₀, hmod₀⟩ := Metric.uniformContinuousOn_iff.mp huc e hepos
  have hcore {x y : HUpper n} (hx : x ∈ truncatedSet hn Γ T.source.centers T.source.level)
      (hd : dist x y < min 1 d₀) : dist (Φ x) (Φ y) < e := by
    obtain ⟨γ, hγ⟩ := T.source.covers_truncated x hx
    have hxR : dist ((γ : PO n 1) • x) basepointH ≤ R := hR hγ
    have hxy : dist ((γ : PO n 1) • x) ((γ : PO n 1) • y) = dist x y :=
      po_dist_smul hn _ x y
    have hyR : dist ((γ : PO n 1) • y) basepointH ≤ R + 1 := by
      have ht := dist_triangle ((γ : PO n 1) • y) ((γ : PO n 1) • x) basepointH
      rw [dist_comm ((γ : PO n 1) • y) ((γ : PO n 1) • x), hxy] at ht
      have hd1 := lt_of_lt_of_le hd (min_le_left _ _)
      linarith
    have hb := hmod₀ ((γ : PO n 1) • x) (show
        (γ : PO n 1) • x ∈ Metric.closedBall basepointH (R + 1) from
          le_trans hxR (by linarith))
      ((γ : PO n 1) • y) hyR
      (by rw [hxy]; exact lt_of_lt_of_le hd (min_le_right _ _))
    have he' (z : HUpper n) : Φ ((γ : PO n 1) • z) = (f γ : PO n 1) • Φ z := he γ z
    rw [he', he', po_dist_smul hn] at hb
    exact hb
  choose d hd hmod using fun i : T.source.centers =>
    Metric.uniformContinuous_iff.mp (T.cuspMap i).uniform_toFun e hepos
  let S : Finset ℝ := insert 1 (Finset.univ.image d)
  have hSne : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let q := S.min' hSne
  have hq : 0 < q := by
    apply (Finset.lt_min'_iff S hSne).mpr
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · norm_num
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      exact hd i
  have hqi (i : T.source.centers) : q ≤ d i :=
    S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hsep : 0 < (ε - r) / 2 := by linarith
  refine ⟨min (min 1 d₀) (min ((ε - r) / 2) q),
    lt_min (lt_min (by norm_num) hd₀) (lt_min hsep hq), ?_⟩
  intro x y hxy
  have hdcore : dist x y < min 1 d₀ := lt_of_lt_of_le hxy (min_le_left _ _)
  by_cases hx : x ∈ truncatedSet hn Γ T.source.centers T.source.level
  · exact hcore hx hdcore
  by_cases hy : y ∈ truncatedSet hn Γ T.source.centers T.source.level
  · rw [dist_comm]
    exact hcore hy (by rwa [dist_comm])
  have hxo : x ∈ openCuspSet hn Γ T.source.centers T.source.level := not_not.mp hx
  have hyo : y ∈ openCuspSet hn Γ T.source.centers T.source.level := not_not.mp hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxo
  obtain ⟨γ, v, hv, hvx⟩ := mem_iUnion.mp hi
  obtain ⟨j, hj⟩ := mem_iUnion.mp hyo
  obtain ⟨δ, w, hw, hwy⟩ := mem_iUnion.mp hj
  have hxa : x ∈ pieceSet T.source (i, γ) :=
    ⟨v, show busemann i.val v ≤ T.source.level i from le_of_lt hv, hvx⟩
  have hyb : y ∈ pieceSet T.source (j, δ) :=
    ⟨w, show busemann j.val w ≤ T.source.level j from le_of_lt hw, hwy⟩
  have hdist : dist x y < (ε - r) / 2 :=
    lt_of_lt_of_le hxy ((min_le_right _ _).trans (min_le_left _ _))
  have hab := pieceSet_eq_of_center_eq T.source hΓ (i, γ) (j, δ)
    (center_eq_of_close T.source hΓ hre hgeom hxa hyb hdist)
  rw [hpiece _ x hxa, hpiece _ y (hab.symm ▸ hyb)]
  change dist ((f γ : PO n 1) • (T.cuspMap i).toEquiv ((γ : PO n 1)⁻¹ • x))
    ((f γ : PO n 1) • (T.cuspMap i).toEquiv ((γ : PO n 1)⁻¹ • y)) < e
  rw [po_dist_smul hn]
  apply hmod i
  rw [po_dist_smul hn]
  exact lt_of_lt_of_le hxy ((min_le_right _ _).trans ((min_le_right _ _).trans (hqi i)))

theorem pieceMap_mem_target (T : MatchedTruncation hn Γ Λ f r)
    (a : Piece T.source) {x : HUpper n} (hx : x ∈ pieceSet T.source a) :
    pieceMap T a x ∈ pieceSet T.target (T.centersEquiv a.1, f a.2) := by
  let v := (poMulAction hn).smul (a.2 : PO n 1)⁻¹ x
  have hv : v ∈ horoball a.1.val (T.source.level a.1) := (mem_pieceSet_iff _ _ _).mp hx
  have him : (T.cuspMap a.1).toEquiv v ∈
      horoball (T.centersEquiv a.1).val (T.target.level (T.centersEquiv a.1)) := by
    rw [← T.image_horoball]
    exact mem_image_of_mem _ hv
  exact ⟨(T.cuspMap a.1).toEquiv v, him, rfl⟩

theorem inverse_pieceMap (T : MatchedTruncation hn Γ Λ f r)
    (a : Piece T.source) (x : HUpper n) :
    pieceMap T.symm (T.centersEquiv a.1, f a.2) (pieceMap T a x) = x := by
  let := poMulAction hn
  change (f.symm (f a.2) : PO n 1) •
    (T.symm.cuspMap (T.centersEquiv a.1)).toEquiv
      ((f a.2 : PO n 1)⁻¹ • ((f a.2 : PO n 1) •
        (T.cuspMap a.1).toEquiv ((a.2 : PO n 1)⁻¹ • x))) = x
  rw [T.symm_cuspMap, T.centersEquiv.symm_apply_apply, f.symm_apply_apply,
    inv_smul_smul, Equiv.symm_apply_apply, smul_inv_smul]

theorem cusp_surjective_of_formulas (T : MatchedTruncation hn Γ Λ f r)
    {Φ : HUpper n → HUpper n}
    (hΦ : ∀ (a : Piece T.source) (x : HUpper n),
      x ∈ pieceSet T.source a → Φ x = pieceMap T a x)
    {y : HUpper n} (hy : y ∈ cuspSet T.target) :
    ∃ x ∈ cuspSet T.source, Φ x = y := by
  let := poMulAction hn
  obtain ⟨⟨j, δ⟩, w, hw, hwy⟩ := mem_iUnion.mp hy
  let i := T.centersEquiv.symm j
  have hi : T.centersEquiv i = j := T.centersEquiv.apply_symm_apply j
  have hw' : w ∈ (T.cuspMap i).toEquiv '' horoball i.val (T.source.level i) := by
    rw [T.image_horoball, hi]
    exact hw
  obtain ⟨v, hv, hvw⟩ := hw'
  let a : Piece T.source := (i, f.symm δ)
  let x := (f.symm δ : PO n 1) • v
  have hxa : x ∈ pieceSet T.source a := ⟨v, hv, rfl⟩
  refine ⟨x, mem_iUnion.mpr ⟨a, hxa⟩, ?_⟩
  rw [hΦ a x hxa]
  change (f (f.symm δ) : PO n 1) • (T.cuspMap i).toEquiv
    ((f.symm δ : PO n 1)⁻¹ • ((f.symm δ : PO n 1) • v)) = y
  rw [inv_smul_smul, f.apply_symm_apply, hvw]
  exact hwy

theorem compositions_eq_on_cusps (T : MatchedTruncation hn Γ Λ f r)
    {Φ Ψ : HUpper n → HUpper n}
    (hΦ : ∀ (a : Piece T.source) (x : HUpper n),
      x ∈ pieceSet T.source a → Φ x = pieceMap T a x)
    (hΨ : ∀ (b : Piece T.target) (y : HUpper n),
      y ∈ pieceSet T.target b → Ψ y = pieceMap T.symm b y) :
    (∀ x ∈ cuspSet T.source, Ψ (Φ x) = x) ∧
      (∀ y ∈ cuspSet T.target, Φ (Ψ y) = y) := by
  have hleft (x : HUpper n) (hx : x ∈ cuspSet T.source) : Ψ (Φ x) = x := by
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    rw [hΦ a x ha, hΨ _ _ (pieceMap_mem_target T a ha)]
    exact inverse_pieceMap T a x
  refine ⟨hleft, fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := cusp_surjective_of_formulas T hΦ hy
  rw [hleft x hx]

theorem exists_composition_bound (D : FiniteCuspTruncation hn Γ r)
    {Φ Ψ : HUpper n → HUpper n} (hΦc : Continuous Φ) (hΨc : Continuous Ψ)
    (hΦe : IsFEquivariant f hn Φ) (hΨe : IsFEquivariant f.symm hn Ψ)
    (hcomp : ∀ x ∈ cuspSet D, Ψ (Φ x) = x) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x, dist (Ψ (Φ x)) x ≤ E := by
  let := poMulAction hn
  have hcont : Continuous (fun x : HUpper n => dist (Ψ (Φ x)) x) :=
    (hΨc.comp hΦc).dist continuous_id
  obtain ⟨B, hB⟩ := (D.compact_core.image hcont).bddAbove
  refine ⟨max 0 B, le_max_left _ _, fun x => ?_⟩
  by_cases hx : x ∈ cuspSet D
  · rw [hcomp x hx, dist_self]
    exact le_max_left _ _
  have ht : x ∈ truncatedSet hn Γ D.centers D.level := fun ho =>
    hx (interior_subset (openCuspSet_subset_interior D ho))
  obtain ⟨γ, hγ⟩ := D.covers_truncated x ht
  have hΦγ : Φ ((γ : PO n 1) • x) = (f γ : PO n 1) • Φ x := hΦe γ x
  have hΨγ : Ψ ((f γ : PO n 1) • Φ x) = (γ : PO n 1) • Ψ (Φ x) := by
    have h := hΨe (f γ) (Φ x)
    rw [f.symm_apply_apply] at h
    exact h
  have hbound : dist (Ψ (Φ ((γ : PO n 1) • x))) ((γ : PO n 1) • x) ≤ B :=
    hB ⟨(γ : PO n 1) • x, hγ, rfl⟩
  rw [hΦγ, hΨγ, po_dist_smul hn] at hbound
  exact hbound.trans (le_max_right _ _)

theorem exists_twoSided_uniform_maps (T : MatchedTruncation hn Γ Λ f r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) (hΛ : IsDiscrete (SetLike.coe Λ))
    {ε : ℝ} (hre : r < ε)
    (hgeomΓ : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (hgeomΛ : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Λ ε x)) :
    ∃ (Φ Ψ : HUpper n → HUpper n) (E E' : ℝ),
      UniformContinuous Φ ∧ UniformContinuous Ψ ∧
      IsFEquivariant f hn Φ ∧ IsFEquivariant f.symm hn Ψ ∧
      0 ≤ E ∧ 0 ≤ E' ∧
      (∀ x, dist (Ψ (Φ x)) x ≤ E) ∧ (∀ y, dist (Φ (Ψ y)) y ≤ E') ∧
      (∀ (a : Piece T.source) (x : HUpper n),
        x ∈ pieceSet T.source a → Φ x = pieceMap T a x) ∧
      (∀ (b : Piece T.target) (y : HUpper n),
        y ∈ pieceSet T.target b → Ψ y = pieceMap T.symm b y) := by
  obtain ⟨Φ, hΦc, hΦe, hΦ⟩ := exists_continuous_global_map T hΓ hre hgeomΓ
  obtain ⟨Ψ, hΨc, hΨe, hΨ⟩ := exists_continuous_global_map T.symm hΛ hre hgeomΛ
  have hΦu := uniformContinuous_of_cusp_formulas T hΓ hre hgeomΓ hΦc hΦe hΦ
  have hΨu := uniformContinuous_of_cusp_formulas T.symm hΛ hre hgeomΛ hΨc hΨe hΨ
  obtain ⟨hleft, hright⟩ := compositions_eq_on_cusps T hΦ hΨ
  obtain ⟨E, hE, hbound⟩ := exists_composition_bound T.source hΦc hΨc hΦe hΨe hleft
  obtain ⟨E', hE', hbound'⟩ := exists_composition_bound T.target hΨc hΦc hΨe
    (by simpa only [MulEquiv.symm_symm] using hΦe) hright
  exact ⟨Φ, Ψ, E, E', hΦu, hΨu, hΦe, hΨe, hE, hE', hbound, hbound', hΦ, hΨ⟩

theorem exists_twoSided_pseudoIsometry (T : MatchedTruncation hn Γ Λ f r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) (hΛ : IsDiscrete (SetLike.coe Λ))
    {ε : ℝ} (hre : r < ε)
    (hgeomΓ : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (hgeomΛ : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Λ ε x)) :
    ∃ (Φ Ψ : HUpper n → HUpper n) (K C C' E E' : ℝ),
      IsPseudoIsometry K C Φ ∧ IsPseudoIsometry K C' Ψ ∧
      UniformContinuous Φ ∧ UniformContinuous Ψ ∧
      IsFEquivariant f hn Φ ∧ IsFEquivariant f.symm hn Ψ ∧
      (∀ x, dist (Ψ (Φ x)) x ≤ E) ∧ (∀ y, dist (Φ (Ψ y)) y ≤ E') ∧
      (∀ (a : Piece T.source) (x : HUpper n),
        x ∈ pieceSet T.source a → Φ x = pieceMap T a x) ∧
      (∀ (b : Piece T.target) (y : HUpper n),
        y ∈ pieceSet T.target b → Ψ y = pieceMap T.symm b y) := by
  obtain ⟨Φ, Ψ, E, E', hΦu, hΨu, hΦe, hΨe, hE, hE', hleft, hright, hΦ, hΨ⟩ :=
    exists_twoSided_uniform_maps T hΓ hΛ hre hgeomΓ hgeomΛ
  obtain ⟨K, C, C', hPI, hPI'⟩ :=
    DifferentialGeometry.UniformCoarseMaps.exists_twoSided_pseudoIsometry hΦu hΨu hE hE' hleft hright
  exact ⟨Φ, Ψ, K, C, C', E, E', hPI, hPI', hΦu, hΨu, hΦe, hΨe, hleft, hright, hΦ, hΨ⟩

theorem exists_equivariant_controlled_boundary_extension
    (T : MatchedTruncation hn Γ Λ f r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) (hΛ : IsDiscrete (SetLike.coe Λ))
    {ε : ℝ} (hre : r < ε)
    (hgeomΓ : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (hgeomΛ : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Λ ε x)) :
    ∃ (Φ : HUpper n → HUpper n) (K C : ℝ) (φ : BoundaryH n ≃ₜ BoundaryH n),
      UniformContinuous Φ ∧ IsPseudoIsometry K C Φ ∧ IsFEquivariant f hn Φ ∧
      BoundaryDistortion.HasCrossRatioControl φ ∧
      BoundaryDistortion.HasCrossRatioControl φ.symm ∧
      (∀ (γ : Γ) (ξ : BoundaryH n),
        φ ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ) =
          (poBoundaryMulAction hn).smul (f γ : PO n 1) (φ ξ)) ∧
      (∀ ξ : BoundaryH n, BoundaryTopology.ConvergesToBoundary
        (fun k : ℕ => Φ (BoundaryTopology.geodesicRay ξ (k : ℝ))) (φ ξ)) := by
  obtain ⟨Φ, Ψ, K, C, C', E, E', hPI, hPI', hΦu, _, hΦe, _, hleft, hright, _, _⟩ :=
    exists_twoSided_pseudoIsometry T hΓ hΛ hre hgeomΓ hgeomΛ
  refine ⟨Φ, K, C, BoundaryHomeomorph.bExtHomeomorph hPI hPI' hleft hright hn,
    hΦu, hPI, hΦe,
    BoundaryDistortion.bExtHomeomorph_hasCrossRatioControl hPI hPI' hleft hright hn,
    BoundaryDistortion.bExtHomeomorph_symm_hasCrossRatioControl hPI hPI' hleft hright hn,
    ?_, ?_⟩
  · intro γ ξ
    simp only [BoundaryHomeomorph.bExtHomeomorph_apply]
    exact BoundaryExtension.bExt_equivariant hPI
      (BoundaryHomeomorph.gromovCauchy_image_ray hPI hn) hn hΦe γ ξ
  · intro ξ
    rw [BoundaryHomeomorph.bExtHomeomorph_apply]
    simpa only [MorseStability.rayTo_basepointH_eq_geodesicRay] using
      BoundaryExtension.bExt_spec (BoundaryHomeomorph.gromovCauchy_image_ray hPI hn) ξ

theorem exists_equivariant_homeomorph_boundary_extension
    (T : MatchedTruncation hn Γ Λ f r)
    (hΓ : IsDiscrete (SetLike.coe Γ)) (hΛ : IsDiscrete (SetLike.coe Λ))
    {ε : ℝ} (hre : r < ε)
    (hgeomΓ : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (hgeomΛ : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Λ ε x)) :
    ∃ (Φ : HUpper n → HUpper n) (K C : ℝ) (φ : BoundaryH n ≃ₜ BoundaryH n),
      UniformContinuous Φ ∧ IsPseudoIsometry K C Φ ∧ IsFEquivariant f hn Φ ∧
      (∀ (γ : Γ) (ξ : BoundaryH n),
        φ ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ) =
          (poBoundaryMulAction hn).smul (f γ : PO n 1) (φ ξ)) ∧
      (∀ ξ : BoundaryH n, BoundaryTopology.ConvergesToBoundary
        (fun k : ℕ => Φ (BoundaryTopology.geodesicRay ξ (k : ℝ))) (φ ξ)) := by
  obtain ⟨Φ, K, C, φ, hΦu, hPI, hΦe, _, _, hφe, hφc⟩ :=
    exists_equivariant_controlled_boundary_extension T hΓ hΛ hre hgeomΓ hgeomΛ
  exact ⟨Φ, K, C, φ, hΦu, hPI, hΦe, hφe, hφc⟩

end DifferentialGeometry.CuspCoarseMaps
