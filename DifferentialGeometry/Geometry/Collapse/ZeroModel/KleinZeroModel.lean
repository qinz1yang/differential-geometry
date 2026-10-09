import DifferentialGeometry.Geometry.Collapse.ZeroModel.KleinLens

/-!
# Q2: the Klein row of LFR52/LFR54 — `D(V) ≅ mobiusBundleCarrier`

Lane LFR54-QUOT, frozen statement Q2 of `build-logs/scratch/F7-LFR51/QuotInputs.lean`
(blueprint master207A, LFR52 (LFR52.2) and LFR54 (LFR54.1), the type `D(o(K))`).

Let `V → B` be a smooth Riemannian line bundle over a surface and `ν : T² → TotalSpace F V` a smooth
injective map onto the unit sphere bundle with `ν (x + ½, -y) = -ν (x, y)` and `proj ∘ ν` a local
diffeomorphism. Then the closed unit disc bundle `D(V)` (native boundary charts) is diffeomorphic to
the fixed twisted `I`-bundle model `GC.Seifert.mobiusBundleCarrier`
(`nonempty_mobiusBundleCarrier_diffeomorph_of_klein_unit_map`).

Route: `D(V) = (T² × [-1, 1]) / ((x, y, t) ∼ (x + ½, -y, -t))` through `(p, t) ↦ t • ν p`
(`RankOneQuotient`), and the same quotient is `{Q ≤ 0} ⊆ L(4, -1)` through the explicit
parametrisation `kleinTheta` (`KleinLens`); the inverse is `kleinLensMap`. Both maps are smooth on
the ambient manifolds, so they restrict to a diffeomorphism of the two regular sublevels with
their boundary charts.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Module Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel.Klein

open GC.Seifert DifferentialGeometry.Topology
open DifferentialGeometry.Topology.VectorBundle.RankOneQuotient

universe u

local notation "S3" => sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {B : Type*} [TopologicalSpace B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- `kleinLensMap ∘ kleinTheta = Φ`. -/
theorem kleinLensMap_kleinTheta (ν : T2 → TotalSpace F V)
    (hνneg : ∀ p, ν (kleinDeck p) = ⟨(ν p).proj, -(ν p).2⟩) (q : T2 × ℝ) :
    kleinLensMap.{u} ν hνneg (kleinTheta.{u} q) = rankOneParam ν q := by
  rw [kleinTheta, kleinLensMap_lensUp, kleinSphereMap_of_ne ν (sq_sub_sq_kleinRepSphere q),
    modelPoint_kleinRepSphere, kleinCoordMap]
  dsimp only
  have hρ : 0 < √(kleinRho (AddCircle.toCircle q.1.2 : ℂ) q.2) :=
    Real.sqrt_pos.mpr (kleinRho_pos _ _)
  rw [circleArg_toCircle, kleinU, circleArg_ofReal_mul hρ, circleArg_toCircle, ← kleinU,
    kleinT_kleinU (Circle.norm_coe _)]

/-- Points of the model region are images of `S³` points with `Q ≤ 0`. -/
theorem exists_sphere_rep_lensUp (y : mobiusBundleSet.{u}) :
    ∃ x : S3, y.val = lensUp (mobiusLensGroup.projection x) ∧
      (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0 ∧ bundleQuartic (lensPair x) ≤ 0 := by
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  refine ⟨x, ?_, sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq, hq⟩
  rw [← hx]
  rfl

/-- `kleinTheta` inverts `kleinLensMap` off `{w₁² = w₂²}`. -/
theorem kleinTheta_coords_eq {x : S3}
    (hx : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0) :
    kleinTheta.{u} ((circleArg (modelPoint (lensPair x)).1, circleArg (modelPoint (lensPair x)).2),
        kleinT (modelPoint (lensPair x)).2) = lensUp (mobiusLensGroup.projection x) := by
  rw [kleinTheta]
  congr 1
  refine (projection_eq_of_modelPoint hx (sq_sub_sq_kleinRepSphere _) (Or.inl ?_)).symm
  rw [modelPoint_kleinRepSphere]
  have hz := modelFibrePoint_ne_zero hx
  have hu := modelAnnulusPoint_ne_zero hx
  change ((AddCircle.toCircle (circleArg (modelFibrePoint (lensPair x))) : ℂ),
      kleinU (AddCircle.toCircle (circleArg (modelAnnulusPoint (lensPair x))))
        (kleinT (modelAnnulusPoint (lensPair x)))) =
    (modelFibrePoint (lensPair x), modelAnnulusPoint (lensPair x))
  rw [coe_toCircle_circleArg hz, coe_toCircle_circleArg hu, kleinU_kleinT hu,
    norm_modelFibrePoint hx, Complex.ofReal_one, div_one]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem kleinLensMap_lensUp_of_ne (ν : T2 → TotalSpace F V)
    (hνneg : ∀ p, ν (kleinDeck p) = ⟨(ν p).proj, -(ν p).2⟩) {x : S3}
    (hx : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0) :
    kleinLensMap.{u} ν hνneg (lensUp (mobiusLensGroup.projection x)) =
      rankOneParam ν ((circleArg (modelPoint (lensPair x)).1,
        circleArg (modelPoint (lensPair x)).2), kleinT (modelPoint (lensPair x)).2) := by
  rw [kleinLensMap_lensUp, kleinSphereMap_of_ne ν hx]
  rfl

/-- On the model region the radial coordinate has absolute value at most one. -/
theorem abs_kleinT_le_one {x : S3} (hq : bundleQuartic (lensPair x) ≤ 0) :
    |kleinT (modelPoint (lensPair x)).2| ≤ 1 := by
  have hab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq
  change |kleinT (modelAnnulusPoint (lensPair x))| ≤ 1
  rw [← norm_joukowski_le_three_iff (modelAnnulusPoint_ne_zero hab)]
  rw [joukowski_modelAnnulusPoint hab]
  exact (bundleQuartic_nonpos_iff hab).mp hq

end DifferentialGeometry.Geometry.Collapse.ZeroModel.Klein

namespace DifferentialGeometry.Topology.VectorBundle

open GC.Seifert DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Geometry.Collapse.ZeroModel.Klein
open DifferentialGeometry.Topology.VectorBundle.RankOneQuotient

universe u

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

/-- A bundle over a surface with total dimension `2 + 1` has rank one. -/
theorem finrank_eq_one_of_finrank_surface_prod (hd : Module.finrank ℝ (E2 × F) = 2 + 1) :
    Module.finrank ℝ F = 1 := by
  rw [Module.finrank_prod, finrank_euclideanSpace_fin] at hd
  omega

/-- **Q2 (Klein row).** A Klein-equivariant unit map `ν : T² → S(V)` identifies the closed unit
disc bundle `D(V)` (native boundary charts) with the fixed model `mobiusBundleCarrier`. -/
theorem nonempty_mobiusBundleCarrier_diffeomorph_of_klein_unit_map
    (hd : Module.finrank ℝ (E2 × F) = 2 + 1)
    (ν : T2 → TotalSpace F V) (hν : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν)
    (hνS : ∀ p, ‖(ν p).2‖ = 1) (hνinj : Function.Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z)
    (hνneg : ∀ x y : AddCircle (1 : ℝ),
      ν (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = ⟨(ν (x, y)).proj, -(ν (x, y)).2⟩)
    (hνloc : IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun p => (ν p).proj)) :
    letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
    Nonempty (Diffeomorph GC.Seifert.mobiusBundleCarrier.{u}.model (morseModelWithCornersHalfSpace 2)
      GC.Seifert.mobiusBundleCarrier.{u}.Carrier {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞) := by
  let := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  have hF := finrank_eq_one_of_finrank_surface_prod hd
  have hneg : ∀ p, ν (kleinDeck p) = ⟨(ν p).proj, -(ν p).2⟩ := fun p => hνneg p.1 p.2
  obtain ⟨φ, hφ, hφs⟩ := exists_contMDiff_rankOneDescend hF ν hν hνS hνinj hνsurj kleinDeck hneg
    hνloc kleinTheta.{u} contMDiff_kleinTheta (fun p t => kleinTheta_deck p t)
  let ψ := kleinLensMap.{u} ν hneg
  have hsurj := rankOneParam_surjective ν hF hνsurj
  have hψφ : ∀ z, ψ (φ z) = z := by
    intro z
    obtain ⟨q, rfl⟩ := hsurj z
    rw [hφ]
    exact kleinLensMap_kleinTheta ν hneg q
  have hφψ : ∀ y : mobiusBundleSet.{u}, φ (ψ y.val) = y.val := by
    intro y
    obtain ⟨x, hy, hx, -⟩ := exists_sphere_rep_lensUp y
    rw [hy]
    change φ (kleinLensMap ν hneg (lensUp (mobiusLensGroup.projection x))) = _
    rw [kleinLensMap_lensUp_of_ne ν hneg hx, hφ]
    exact kleinTheta_coords_eq hx
  have hψS : ∀ y : mobiusBundleSet.{u}, ‖(ψ y.val).2‖ ≤ 1 := by
    intro y
    obtain ⟨x, hy, hx, hq⟩ := exists_sphere_rep_lensUp y
    rw [hy]
    change ‖(kleinLensMap ν hneg (lensUp (mobiusLensGroup.projection x))).2‖ ≤ 1
    rw [kleinLensMap_lensUp_of_ne ν hneg hx, norm_rankOneParam ν hνS]
    exact abs_kleinT_le_one hq
  have hφS : ∀ z : {z : TotalSpace F V // ‖z.2‖ ≤ 1}, φ z.val ∈ mobiusBundleSet.{u} := by
    intro z
    obtain ⟨q, hq⟩ := hsurj z.val
    change mobiusBundleFunction (φ z.val) ≤ 0
    rw [← hq, hφ, mobiusBundleFunction_kleinTheta_nonpos_iff, ← norm_rankOneParam ν hνS, hq]
    exact z.2
  have hψs : ∀ y : mobiusBundleSet.{u},
      ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ψ y.val := by
    intro y
    obtain ⟨x, hy, hx, -⟩ := exists_sphere_rep_lensUp y
    rw [hy]
    exact contMDiffAt_kleinLensMap ν hν hneg hx
  let D : Diffeomorph (𝓡∂ 3) (morseModelWithCornersHalfSpace 2) mobiusBundleSet.{u}
      {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞ :=
    { toFun := fun y => ⟨ψ y.val, hψS y⟩
      invFun := fun z => ⟨φ z.val, hφS z⟩
      left_inv := fun y => Subtype.ext (hφψ y)
      right_inv := fun z => Subtype.ext (hψφ z.val)
      contMDiff_toFun := by
        apply (contMDiff_normClosedDisc_iff (JX := 𝓡∂ 3) hd (R := 1) one_pos).mpr
        intro y
        exact (hψs y).comp y (mobiusBundleAtlas.contMDiff_subtype_val y)
      contMDiff_invFun := by
        apply (mobiusBundleAtlas.contMDiff_iff_subtype_val
          (fun z : {z : TotalSpace F V // ‖z.2‖ ≤ 1} =>
            (⟨φ z.val, hφS z⟩ : mobiusBundleSet.{u}))).mpr
        exact hφs.comp (contMDiff_normClosedDisc_val hd 1 one_pos) }
  exact ⟨D⟩

end DifferentialGeometry.Topology.VectorBundle
