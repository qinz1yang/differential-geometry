import DifferentialGeometry.Geometry.Collapse.ZeroModel.UnitMapClassification
import DifferentialGeometry.Topology.VectorBundle.LineOrientedSurfaceRows
import DifferentialGeometry.Topology.VectorBundle.RankOneQuotient.Descend
import DifferentialGeometry.Topology.VectorBundle.NormPreservingDisc
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels

/-!
# The surface-soul rows of LFR51 (rank-one normal bundles over a closed surface)

Lane LFR54-ROW, group G2. Frozen blueprint master207A, LFR51 (A:29309), table (LFR51.1), rows
`S² | S² × ℝ`, `T² | T² × ℝ`, `ℝP² | o(ℝP²)`, `K | o(K)`, and the identification (LFR51.2)
`Ê ≅ (S̃_or × ℝ)/((x, t) ∼ (τ x, -t))` with the absolute-value fibre norm. For a smooth Riemannian
line bundle `V` over a closed surface `B` (charted on `E2`) with an oriented total space and a
`C^n` base metric of `K ≥ 0` (`n ≥ 2`):

* `rankOneParam_package`: for a unit map `ν : Σ → S(V)` intertwining an involution `τ` with
  `v ↦ -v`, the base is the double cover `proj ∘ ν` with fibres `{p, τ p}`, and
  `Φ (p, t) = t • ν p` is smooth, onto, identifies exactly `(p, t) ∼ (τ p, -t)`, `‖Φ (p, t)‖ = |t|`
  (LFR51.2);
* `nonempty_baseOrientation_of_not_isPreconnected`: a disconnected unit sphere bundle and an
  oriented total space orient the base (the unit sphere bundle is the tangent orientation cover,
  Codex X112);
* `exists_sphereAntipodalQuotient_diffeomorph_of_antipodal_unit_map`: an antipodal unit map
  identifies the base with the fixed `ℝP²` model `SphereAntipodalQuotient`;
* `trivialProdDiffeomorph`, `exists_normClosedDisc_diffeomorph_trivial_of_prod`: product ↔ trivial
  bundle, and the closed disc bundle of a norm-preserving product row is that of the trivial line;
* `exists_surface_soul_bundle_type` (the surface clause of the LFR51 row): `S² × ℝ` or flat
  `T² × ℝ` (disconnected unit sphere bundle, closed disc bundle = that of the trivial line), or
  `o(ℝP²)` (base `≅ ℝP²`), or `o(K)` (base the double cover `T² → B` with deck
  `(x, y) ↦ (x + ½, -y)`), each with its (LFR51.2) identification.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Module
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

open DifferentialGeometry.Topology DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.VectorBundle.RankOneQuotient
open DifferentialGeometry.Topology.Manifold

local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)
local notation "RP2" =>
  DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient

section Product

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB)
  (B : Type*) [TopologicalSpace B] [ChartedSpace HB B]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The product `B × E` is the total space of the trivial bundle (`(b, x) ↦ ⟨b, x⟩`). -/
def trivialProdDiffeomorph :
    Diffeomorph (IB.prod 𝓘(ℝ, E)) (IB.prod 𝓘(ℝ, E)) (B × E) (TotalSpace E (Trivial B E)) ∞ where
  toFun z := ⟨z.1, z.2⟩
  invFun z := (z.proj, z.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_fst, ?_⟩
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply]
    exact contMDiffAt_snd
  contMDiff_invFun := by
    intro z
    let trivAtlas_LFR54ROW : MemTrivializationAtlas (Trivial.trivialization B E) :=
      ⟨Set.mem_singleton _⟩
    have h := (Trivial.trivialization B E).contMDiffOn (IB := IB) (n := ∞)
    exact h.contMDiffAt (by simpa only [Trivial.trivialization_source] using Filter.univ_mem)

@[simp] theorem trivialProdDiffeomorph_apply (z : B × E) :
    trivialProdDiffeomorph IB B E z = (⟨z.1, z.2⟩ : TotalSpace E (Trivial B E)) := rfl

end Product

section Package

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] {HS : Type*} [TopologicalSpace HS]
  {IS : ModelWithCorners ℝ ES HS} {S : Type*} [TopologicalSpace S] [ChartedSpace HS S]

/-- **(LFR51.2) for a unit map.** A smooth injective unit map `ν : Σ → S(V)` onto the unit sphere
bundle of a line bundle, intertwining `τ` with `v ↦ -v`: the base is the double cover
`proj ∘ ν` with fibres `{p, τ p}`; `Φ (p, t) = t • ν p` is smooth and onto, identifies exactly
`(p, t)` with `(τ p, -t)`, and carries `|t|` to the fibre norm. -/
theorem rankOneParam_package (h1 : finrank ℝ F = 1)
    (ν : S → TotalSpace F V) (hν : ContMDiff IS (IB.prod 𝓘(ℝ, F)) ∞ ν)
    (hνS : ∀ p, ‖(ν p).2‖ = 1) (hνinj : Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z)
    (τ : S → S) (hνneg : ∀ p, ν (τ p) = ⟨(ν p).proj, -(ν p).2⟩) :
    Surjective (fun p => (ν p).proj) ∧
    (∀ p p' : S, (ν p').proj = (ν p).proj ↔ p' = p ∨ p' = τ p) ∧
    ContMDiff (IS.prod 𝓘(ℝ, ℝ)) (IB.prod 𝓘(ℝ, F)) ∞ (rankOneParam ν) ∧
    Surjective (rankOneParam ν) ∧
    (∀ q q' : S × ℝ, rankOneParam ν q' = rankOneParam ν q ↔ q' = q ∨ q' = (τ q.1, -q.2)) ∧
    ∀ q : S × ℝ, ‖(rankOneParam ν q).2‖ = |q.2| := by
  refine ⟨fun b => ?_, fun p p' => ⟨eq_or_eq_of_proj_eq ν τ h1 hνS hνinj hνneg, ?_⟩, ?_,
    rankOneParam_surjective ν h1 hνsurj, fun q q' => ⟨rankOneParam_eq_iff ν τ h1 hνS hνinj hνneg,
      ?_⟩, norm_rankOneParam ν hνS⟩
  · obtain ⟨u, hu⟩ := exists_norm_eq_one_of_finrank_eq_one ((finrank_fiber (F := F) (V := V) b).trans h1)
    obtain ⟨p, hp⟩ := hνsurj ⟨b, u⟩ hu
    exact ⟨p, congrArg TotalSpace.proj hp⟩
  · rintro (rfl | rfl)
    · rfl
    · rw [hνneg p]
  · have hs := DifferentialGeometry.Geometry.Collapse.contMDiff_totalSpace_smul (IB := IB) (F := F)
      (V := V)
    exact hs.comp (contMDiff_snd.prodMk (hν.comp contMDiff_fst))
  · rintro (rfl | rfl)
    · rfl
    · exact rankOneParam_deck ν τ hνneg q.1 q.2

end Package

section Surface

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

/-- **A disconnected unit sphere bundle orients the base.** For a line bundle over a compact
connected surface with an oriented total space, the unit sphere bundle is the tangent orientation
double cover (X112); if it is not preconnected, the base is orientable. -/
theorem nonempty_baseOrientation_of_not_isPreconnected [CompactSpace B] [T2Space B]
    [ConnectedSpace B] (h1 : finrank ℝ F = 1)
    (o : ManifoldOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) 3)
    (hS : ¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}) :
    Nonempty (ManifoldOrientation (𝓡 2) B 2) := by
  have h2 : finrank ℝ E2 = 2 := finrank_euclideanSpace_fin
  let contMetric_LFR54ROW : IsContinuousRiemannianBundle F V :=
    isContinuousRiemannianBundle_of_contMDiff (EB := E2)
  have hnot : ¬ ConnectedSpace (tangentOrientationCover (M := B) h2) := by
    intro hc
    apply hS
    have hcon : ConnectedSpace {z : TotalSpace F V // ‖z.2‖ = 1} :=
      (unitTangentCoverHomeomorph h2 h1 o).symm.surjective.connectedSpace
        (unitTangentCoverHomeomorph h2 h1 o).symm.continuous
    exact isPreconnected_iff_preconnectedSpace.mpr hcon.toPreconnectedSpace
  obtain ⟨or, hor⟩ := exists_compatibleOrientation_of_orientationCover_not_connected h2 hnot
  exact exists_manifoldOrientation_of_compatibleOrientation h2 or hor

omit [FiniteDimensional ℝ F] [IsManifold (𝓡 2) ∞ B] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V] in
/-- **The `ℝP²` base.** An antipodal unit map identifies the base with the fixed `ℝP²` model
`SphereAntipodalQuotient`, the class of `x` corresponding to the base point of `ν x`. -/
theorem exists_sphereAntipodalQuotient_diffeomorph_of_antipodal_unit_map
    (h1 : finrank ℝ F = 1)
    (ν : S2 → TotalSpace F V) (hνS : ∀ x, ‖(ν x).2‖ = 1) (hνinj : Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z)
    (hνneg : ∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩)
    (hνloc : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj)) :
    ∃ h : Diffeomorph (𝓡 2) (𝓡 2) B RP2 ∞, ∀ x,
      h (ν x).proj =
        DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj x := by
  classical
  let q : S2 → RP2 :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj
  have hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.isLocalDiffeomorph_proj
  have hqs : Surjective q :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.surjective_proj
  let p : S2 → B := fun x => (ν x).proj
  have hps : Surjective p := by
    intro b
    obtain ⟨u, hu⟩ :=
      exists_norm_eq_one_of_finrank_eq_one ((finrank_fiber (F := F) (V := V) b).trans h1)
    obtain ⟨x, hx⟩ := hνsurj ⟨b, u⟩ hu
    exact ⟨x, by simp only [p, hx]⟩
  have hrel : ∀ x y, p x = p y ↔ q x = q y := by
    intro x y
    rw [DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj_eq_iff]
    constructor
    · intro h
      exact eq_or_eq_of_proj_eq ν (fun x => -x) h1 hνS hνinj hνneg h.symm
    · rintro (rfl | rfl)
      · rfl
      · change (ν x).proj = (ν (-x)).proj
        rw [hνneg x]
  -- the map `B → ℝP²` through local inverses of `p`
  let f : B → RP2 := q ∘ surjInv hps
  have hf : ∀ x, f (p x) = q x := fun x =>
    (hrel (surjInv hps (p x)) x).mp (surjInv_eq hps (p x))
  have hinj : Injective f := by
    intro a b hab
    have he := (hrel (surjInv hps a) (surjInv hps b)).mpr hab
    simpa only [surjInv_eq] using he
  have hsurj : Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := hqs y
    exact ⟨p x, hf x⟩
  let e : B ≃ RP2 := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have he : ∀ x, e (p x) = q x := hf
  have hinv : ∀ x, e.symm (q x) = p x := by
    intro x
    rw [← he x, e.symm_apply_apply]
  refine ⟨{ toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }, he⟩
  · apply hνloc.contMDiff_of_comp_of_surjective hps
    have hc : (e : B → RP2) ∘ p = q := funext he
    rw [hc]
    exact hq.contMDiff
  · apply hq.contMDiff_of_comp_of_surjective hqs
    have hc : (e.symm : RP2 → B) ∘ q = p := funext hinv
    rw [hc]
    exact hνloc.contMDiff

/-- `dim (ℝ² × ℝ¹) = 2 + 1`. -/
theorem finrank_euclideanTwo_prod_one : finrank ℝ (E2 × E1) = 2 + 1 := by
  rw [finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]

/-- `dim ((ℝ × ℝ) × ℝ¹) = 2 + 1`. -/
theorem finrank_real_prod_real_prod_one : finrank ℝ ((ℝ × ℝ) × E1) = 2 + 1 := by
  rw [finrank_prod, finrank_prod, finrank_self, finrank_euclideanSpace_fin]

/-- **The surface clause of LFR51.** A smooth Riemannian line bundle over a compact connected
surface (charted on `E2`) with an oriented total space and a `C^n` base metric of `K ≥ 0`
(`n ≥ 2`) is one of the four rank-one rows of (LFR51.1):
* `S² × ℝ` (unit sphere bundle not preconnected), norm-preserving, and `D(Ê)` is the closed unit
  disc bundle of the trivial line over `S²`, through the same map;
* `T² × ℝ` with the base metric flat (unit sphere bundle not preconnected), likewise;
* `o(ℝP²)`: an antipodal unit map `ν`, the base `≅ ℝP²` (`SphereAntipodalQuotient`) with `[x] ↔ ν x`,
  and (LFR51.2) `Ê ≅ (S² × ℝ)/((x, t) ∼ (-x, -t))`, fibre norm `|t|`;
* `o(K)`: a Klein unit map `ν`, the base the double cover `proj ∘ ν : T² → B` with fibres
  `{p, (p₁ + ½, -p₂)}`, and (LFR51.2) `Ê ≅ (T² × ℝ)/((p, t) ∼ ((p₁ + ½, -p₂), -t))`, norm `|t|`. -/
theorem exists_surface_soul_bundle_type [CompactSpace B] [ConnectedSpace B] [T2Space B]
    (hd : finrank ℝ (E2 × F) = 2 + 1)
    (oN : SmoothOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V))
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : B → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    (¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1} ∧
      ∃ Ψ : (S2 × E1) ≃ₘ⟮(𝓡 2).prod (𝓡 1), (𝓡 2).prod 𝓘(ℝ, F)⟯ TotalSpace F V,
        (∀ z, ‖(Ψ z).2‖ = ‖z.2‖) ∧
        letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := Trivial S2 E1)
          finrank_euclideanTwo_prod_one 1 one_pos
        letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
        ∃ Ψ' : Diffeomorph (morseModelWithCornersHalfSpace 2) (morseModelWithCornersHalfSpace 2)
            {z : TotalSpace E1 (Trivial S2 E1) // ‖z.2‖ ≤ 1} {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞,
          ∀ z, (Ψ' z).val = Ψ (z.val.proj, z.val.2)) ∨
    (¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1} ∧
      (∀ (b : B) (v w : TangentSpace (𝓡 2) b), k.sectionalCurvature b v w = 0) ∧
      ∃ Ψ : (T2 × E1) ≃ₘ⟮(𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 1), (𝓡 2).prod 𝓘(ℝ, F)⟯ TotalSpace F V,
        (∀ z, ‖(Ψ z).2‖ = ‖z.2‖) ∧
        letI := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
          (V := Trivial T2 E1) finrank_real_prod_real_prod_one 1 one_pos
        letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
        ∃ Ψ' : Diffeomorph (morseModelWithCornersHalfSpace 2) (morseModelWithCornersHalfSpace 2)
            {z : TotalSpace E1 (Trivial T2 E1) // ‖z.2‖ ≤ 1} {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞,
          ∀ z, (Ψ' z).val = Ψ (z.val.proj, z.val.2)) ∨
    (∃ ν : S2 → TotalSpace F V, ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
      (∀ x, ‖(ν x).2‖ = 1) ∧ Injective ν ∧
      (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z) ∧
      (∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj) ∧
      (∃ h : Diffeomorph (𝓡 2) (𝓡 2) B RP2 ∞, ∀ x, h (ν x).proj =
        DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj x) ∧
      ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ (rankOneParam ν) ∧
      Surjective (rankOneParam ν) ∧
      (∀ q q' : S2 × ℝ, rankOneParam ν q' = rankOneParam ν q ↔ q' = q ∨ q' = (-q.1, -q.2)) ∧
      ∀ q : S2 × ℝ, ‖(rankOneParam ν q).2‖ = |q.2|) ∨
    (∃ ν : T2 → TotalSpace F V, ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
      (∀ p, ‖(ν p).2‖ = 1) ∧ Injective ν ∧
      (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z) ∧
      (∀ x y : AddCircle (1 : ℝ),
        ν (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = ⟨(ν (x, y)).proj, -(ν (x, y)).2⟩) ∧
      IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun p => (ν p).proj) ∧
      Surjective (fun p => (ν p).proj) ∧
      (∀ p p' : T2, (ν p').proj = (ν p).proj ↔
        p' = p ∨ p' = (p.1 + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -p.2)) ∧
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ (rankOneParam ν) ∧
      Surjective (rankOneParam ν) ∧
      (∀ q q' : T2 × ℝ, rankOneParam ν q' = rankOneParam ν q ↔
        q' = q ∨ q' = ((q.1.1 + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -q.1.2), -q.2)) ∧
      ∀ q : T2 × ℝ, ‖(rankOneParam ν q).2‖ = |q.2|) := by
  have h2 : finrank ℝ E2 = 2 := finrank_euclideanSpace_fin
  have h1 : finrank ℝ F = 1 := by
    rw [finrank_prod, h2] at hd
    omega
  by_cases hS : IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}
  · right; right
    rcases exists_antipodal_or_klein_unit_map hd oN hS hn k hK with
      ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc⟩ | ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc⟩
    · left
      obtain ⟨-, -, hs, hsurj, hiff, hnorm⟩ :=
        rankOneParam_package h1 ν hν hνS hνinj hνsurj (fun x => -x) hνneg
      exact ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc,
        exists_sphereAntipodalQuotient_diffeomorph_of_antipodal_unit_map h1 ν hνS hνinj hνsurj
          hνneg hνloc, hs, hsurj, hiff, hnorm⟩
    · right
      obtain ⟨hps, hfib, hs, hsurj, hiff, hnorm⟩ :=
        rankOneParam_package h1 ν hν hνS hνinj hνsurj
          (fun p => (p.1 + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -p.2)) (fun p => hνneg p.1 p.2)
      exact ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc, hps, hfib, hs, hsurj, hiff, hnorm⟩
  · obtain ⟨O, -⟩ := exists_manifoldOrientation_eq_of_smoothOrientation ((𝓡 2).prod 𝓘(ℝ, F)) oN
    have h3 : finrank ℝ (E2 × F) = 3 := hd
    let o3 : ManifoldOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) 3 :=
      Eq.rec (motive := fun m _ => ManifoldOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) m)
        O h3
    obtain ⟨ob⟩ := nonempty_baseOrientation_of_not_isPreconnected h1 o3 hS
    rcases exists_orientable_surface_line_rows ob hn k hK h1 hS with ⟨Ψ, hΨ⟩ | ⟨⟨Ψ, hΨ⟩, hflat⟩
    · left
      let Φ := (trivialProdDiffeomorph (𝓡 2) S2 E1).symm.trans Ψ
      obtain ⟨Ψ', hΨ', -⟩ := exists_normClosedDisc_diffeomorph_of_norm_eq
        finrank_euclideanTwo_prod_one hd Φ (fun z => hΨ _) 1 one_pos
      exact ⟨hS, Ψ, hΨ, Ψ', hΨ'⟩
    · right; left
      let Φ := (trivialProdDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) T2 E1).symm.trans Ψ
      obtain ⟨Ψ', hΨ', -⟩ := exists_normClosedDisc_diffeomorph_of_norm_eq
        finrank_real_prod_real_prod_one hd Φ (fun z => hΨ _) 1 one_pos
      exact ⟨hS, hflat, Ψ, hΨ, Ψ', hΨ'⟩

end Surface

end DifferentialGeometry.Geometry.Collapse.ZeroModel
