import DifferentialGeometry.Topology.Surface.Recognition.SublevelCollarDisk
import DifferentialGeometry.Topology.Surface.Recognition.SphereModelChange
import DifferentialGeometry.Topology.Surface.Recognition.RoundedHeight
import DifferentialGeometry.Topology.Surface.Recognition.DiskSide
import DifferentialGeometry.Topology.HighDimensional.TwistedSphere
import DifferentialGeometry.Topology.Handle.SphereDisk
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleConsequences
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Surface.Recognition.DiskAnnulusSphere

/-!
# LFR24's smooth disk: a topological-disk sublevel with a regular band is a smooth disk (SF6)

Let `f` be smooth on an open set `W` of a boundaryless smooth surface `Z`, `s < s'`, with a smooth
field `Y` on `W` such that `df(Y) > 0` on the compact band `f⁻¹[s, s']`, and suppose the sublevel
`D_s = {f ≤ s}` is a topological closed disk with boundary circle `{f = s}`.  Then `D_s` is the image
of a smooth embedding of the closed unit disk `ClosedCell 2`, with boundary circle onto `{f = s}`.

This is the clause "D_s is a smooth compact disk" of LFR24 (blueprint master207A:26862; Hirsch 9.3.7 in
the blueprint), proved without the classification of surfaces (lane SF-C, route of its sheet):

1. the collar of the band makes `D_{s'}` a topological disk (`exists_disk_sublevel_of_field`);
2. the rounded fibre `Σ = {(x,t) ∈ W × ℝ | f x + t² = s'}` is a regular level set, homeomorphic to
   `S²` (its two halves are copies of `D_{s'}`, `twisted_sphere_homeomorph`), hence diffeomorphic to `S²`
   (`nonempty_diffeomorph_sphereTwo_of_homeomorph`);
3. the level `{f = s}` is a compact connected regular level, a smooth circle (lane N1), embedded in
   the upper half of `Σ`, where the projection to `Z` is a local diffeomorphism (no fold over `D_s`);
4. smooth Schoenflies on `S²` (`exists_two_smooth_disks_sphere_of_circle`) gives two smooth disks; the
   one on the side of `D_s` (`union_eq_range_or_range`) is projected back to `Z`.
-/

set_option autoImplicit false

open Set Metric Function Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ Z] in
/-- A function smooth on an open set `W` with a nonzero differential at `x ∈ W` restricts to a
submersion at `x` on the open submanifold `W`. -/
theorem surjective_mfderiv_restrict_opens {W : TopologicalSpace.Opens Z} {f : Z → ℝ}
    (hfW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f W) (x : W) (hx : ∃ v, mvfderiv (I := I) f x v ≠ 0) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y : W => f y) x) := by
  have hfx : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    ((hfW (x : Z) x.2).contMDiffAt (W.isOpen.mem_nhds x.2)).mdifferentiableAt (by simp)
  have hd : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y : W => f y) x
      ((mfderiv I 𝓘(ℝ, ℝ) f x).comp (ContinuousLinearMap.id ℝ E)) :=
    hfx.hasMFDerivAt.comp x (DifferentialGeometry.hasMFDerivAt_subtype_val (I := I) W x)
  rw [hd.mfderiv]
  obtain ⟨v, hv⟩ := hx
  change Surjective (fun w : E => mvfderiv (I := I) f x w)
  intro y
  refine ⟨(y / mvfderiv (I := I) f x v) • v, ?_⟩
  simp only [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ y hv

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ Z] in
/-- The open unit disk inside `Disk n` is connected. -/
theorem isConnected_diskInterior (n : ℕ) : IsConnected (diskInterior n) := by
  have himage : (Subtype.val : Disk n → EuclideanSpace ℝ (Fin n)) '' diskInterior n =
      ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, ball_subset_closedBall hy⟩, hy, rfl⟩
  have hind : Topology.IsInducing (Subtype.val : Disk n → EuclideanSpace ℝ (Fin n)) :=
    Topology.IsInducing.subtypeVal
  refine ⟨⟨⟨0, by simp⟩, by simp [diskInterior]⟩, ?_⟩
  apply hind.isPreconnected_image.mp
  rw [himage]
  exact (convex_ball (0 : EuclideanSpace ℝ (Fin n)) 1).isPreconnected

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ Z] in
/-- The boundary circle of `Disk 2` is connected. -/
theorem isConnected_diskSphere_two : IsConnected (diskSphere 2) := by
  have himage : (Subtype.val : Disk 2 → EuclideanSpace ℝ (Fin 2)) '' diskSphere 2 =
      sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, sphere_subset_closedBall hy⟩, hy, rfl⟩
  have hind : Topology.IsInducing (Subtype.val : Disk 2 → EuclideanSpace ℝ (Fin 2)) :=
    Topology.IsInducing.subtypeVal
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank]
    simp
  have hc := isConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin 2)) zero_le_one
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := hc.nonempty
    exact ⟨⟨y, sphere_subset_closedBall hy⟩, hy⟩
  · apply hind.isPreconnected_image.mp
    rw [himage]
    exact hc.isPreconnected

/-- **SF6 (LFR24's smooth disk).** On a boundaryless smooth surface, let `f` be smooth on an open set
`W ⊇ {f ≤ s'}` (compact), with a smooth field `Y` on an open `W' ⊇ f⁻¹[s, s']` such that `df(Y) > 0` on
`f⁻¹[s, s']`, `s < s'`.
If `{f ≤ s}` is a topological closed disk with boundary circle `{f = s}`, it is a smooth closed disk:
the image of a smooth embedding of `ClosedCell 2` carrying the boundary circle onto `{f = s}`. -/
theorem exists_smooth_disk_of_sublevel [T2Space Z] [SigmaCompactSpace Z]
    (hE : Module.finrank ℝ E = 2) {f : Z → ℝ} (hf : Continuous f) {W : Set Z} (hW : IsOpen W)
    (hfW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f W) {s s' : ℝ} (hss' : s < s')
    (hcpt : IsCompact {x | f x ≤ s'}) (hsub : {x | f x ≤ s'} ⊆ W)
    {W' : Set Z} (hW' : IsOpen W') (hKW' : f ⁻¹' Icc s s' ⊆ W') (Y : (x : Z) → TangentSpace I x)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I Z)) W')
    (hpos : ∀ x ∈ f ⁻¹' Icc s s', 0 < mvfderiv (I := I) f x (Y x))
    {φ : Disk 2 → Z} (hφ : Continuous φ) (hφ' : Injective φ)
    (hrange : range φ = {x | f x ≤ s}) (hbd : φ '' diskSphere 2 = {x | f x = s}) :
    ∃ b : ClosedCell 2 → Z, Manifold.IsSmoothEmbedding (𝓡∂ 2) I ∞ b ∧ range b = {x | f x ≤ s} ∧
      range (b ∘ cellBoundaryInclusion 2) = {x | f x = s} := by
  classical
  ------------------------------------------------------------------ step 1: `D_{s'}` is a disk
  have hK : IsCompact (f ⁻¹' Icc s s') :=
    hcpt.of_isClosed_subset (isClosed_Icc.preimage hf) fun x hx => hx.2
  have hKW : f ⁻¹' Icc s s' ⊆ W := fun x hx => hsub hx.2
  obtain ⟨φ', hφ'c, hφ'i, hφ'r, hφ'b⟩ :=
    exists_disk_sublevel_of_field (m := 1) hf (hW.inter hW') (hfW.mono inter_subset_left) hss' hK
      (fun x hx => ⟨hKW hx, hKW' hx⟩) Y (hY.mono inter_subset_right) hpos hφ hφ' hrange hbd
  have hdf : ∀ x, f x ∈ Icc s s' → ∃ v, mvfderiv (I := I) f x v ≠ 0 :=
    fun x hx => ⟨Y x, (hpos x hx).ne'⟩
  ------------------------------------------------------------------ step 2: the rounded fibre
  let Wo : TopologicalSpace.Opens Z := ⟨W, hW⟩
  have hfWo : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (Wo : Set Z) := hfW
  let G : Wo × ℝ → ℝ := roundedHeight Wo f
  have hGdef : ∀ p : Wo × ℝ, G p = f p.1 + p.2 ^ 2 := fun _ => rfl
  have hG : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ G := contMDiff_roundedHeight hfWo
  have hGreg : ∀ p, G p = s' → Surjective (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) G p) := by
    intro p hp
    apply surjective_mfderiv_roundedHeight hfWo p
    by_cases h0 : p.2 = 0
    · right
      apply hdf
      rw [hGdef, h0] at hp
      have hfp : f p.1 = s' := by simpa using hp
      exact ⟨by linarith, hfp.le⟩
    · exact Or.inl h0
  let S := {p : Wo × ℝ // G p = s'}
  let _ : ChartedSpace (Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) S :=
    DifferentialGeometry.Topology.Manifold.regularFiberChartedSpace G s' hG hGreg
  have _ : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) ∞ S :=
    DifferentialGeometry.Topology.Manifold.regularFiberIsManifold G s' hG hGreg
  -- the two halves of `S` are copies of `D_{s'}`
  have hφ'le : ∀ x, f (φ' x) ≤ s' := fun x => by
    have hx : φ' x ∈ range φ' := mem_range_self x
    rw [hφ'r] at hx
    exact hx
  have hφ'W : ∀ x, φ' x ∈ W := fun x => hsub (hφ'le x)
  let ht : Disk 2 → ℝ := fun x => √(s' - f (φ' x))
  have hht : ∀ x, f (φ' x) + ht x ^ 2 = s' := fun x => by
    simp only [ht]
    rw [Real.sq_sqrt (by linarith [hφ'le x])]
    ring
  let up : Disk 2 → S := fun x => ⟨(⟨φ' x, hφ'W x⟩, ht x), hht x⟩
  let lo : Disk 2 → S := fun x => ⟨(⟨φ' x, hφ'W x⟩, -ht x), by
    rw [hGdef]
    simp only [neg_sq]
    exact hht x⟩
  have hhtc : Continuous ht := Real.continuous_sqrt.comp (continuous_const.sub (hf.comp hφ'c))
  have hupc : Continuous up := ((hφ'c.subtype_mk hφ'W).prodMk hhtc).subtype_mk _
  have hloc : Continuous lo := ((hφ'c.subtype_mk hφ'W).prodMk hhtc.neg).subtype_mk _
  have hupi : Injective up := fun a b h => hφ'i (congrArg (fun p : S => (p.1.1 : Z)) h)
  have hloi : Injective lo := fun a b h => hφ'i (congrArg (fun p : S => (p.1.1 : Z)) h)
  have hcov : range up ∪ range lo = univ := by
    refine eq_univ_of_forall fun p => ?_
    have hp : f p.1.1 + p.1.2 ^ 2 = s' := p.2
    have hle : f p.1.1 ≤ s' := by nlinarith [sq_nonneg p.1.2]
    obtain ⟨x, hx⟩ : (p.1.1 : Z) ∈ range φ' := by rw [hφ'r]; exact hle
    have hsq : p.1.2 ^ 2 = ht x ^ 2 := by
      have := hht x
      rw [hx] at this
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact Or.inl ⟨x, Subtype.ext (Prod.ext (Subtype.ext hx) h.symm)⟩
    · exact Or.inr ⟨x, Subtype.ext (Prod.ext (Subtype.ext hx) h.symm)⟩
  have hseam : ∀ x, x ∈ diskSphere 2 ↔ ht x = 0 := by
    intro x
    constructor
    · intro hx
      have h4 : φ' x ∈ φ' '' diskSphere 2 := mem_image_of_mem _ hx
      rw [hφ'b] at h4
      have h4' : f (φ' x) = s' := h4
      simp only [ht, h4', sub_self, Real.sqrt_zero]
    · intro h0
      have h4 : f (φ' x) = s' := by
        have := hht x
        rw [h0] at this
        linarith
      have h5 : φ' x ∈ φ' '' diskSphere 2 := by rw [hφ'b]; exact h4
      obtain ⟨z, hz, hzx⟩ := h5
      rwa [← hφ'i hzx]
  have hupl : ∀ x ∈ diskSphere 2, up x = lo x := by
    intro x hx
    apply Subtype.ext
    refine Prod.ext rfl ?_
    change ht x = -ht x
    rw [(hseam x).mp hx, neg_zero]
  have hinter : range up ∩ range lo = up '' diskSphere 2 := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
      have h1 : φ' y = φ' x := congrArg (fun p : S => (p.1.1 : Z)) hy
      have hxy := hφ'i h1
      subst hxy
      have h2 : -ht y = ht y := congrArg (fun p : S => p.1.2) hy
      exact ⟨y, (hseam y).mpr (by linarith), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, ⟨x, (hupl x hx).symm⟩⟩
  have hbdry : up '' diskSphere 2 = lo '' diskSphere 2 := image_congr hupl
  obtain ⟨hS⟩ := twisted_sphere_homeomorph (m := 1) (hupc.isClosedEmbedding hupi)
    (hloc.isClosedEmbedding hloi) hcov hinter hbdry
  have hk : Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ = 2 := by
    simp [Module.finrank_prod, hE]
  obtain ⟨Ψ⟩ := nonempty_diffeomorph_sphereTwo_of_homeomorph hk hS
  ------------------------------------------------------------------ step 3: the level circle
  let fW : Wo → ℝ := fun x => f x
  have hfWs : ContMDiff I 𝓘(ℝ, ℝ) ∞ fW := hfWo.comp_contMDiff contMDiff_subtype_val fun x => x.2
  have hLreg : ∀ x : Wo, fW x = s → Surjective (mfderiv I 𝓘(ℝ, ℝ) fW x) := fun x hx =>
    surjective_mfderiv_restrict_opens hfWo x (hdf x ⟨hx.ge, by
      change f x = s at hx
      linarith⟩)
  have hφle : ∀ x, f (φ x) ≤ s := fun x => by
    have hx : φ x ∈ range φ := mem_range_self x
    rw [hrange] at hx
    exact hx
  have hlevW : ∀ y : Z, f y = s → y ∈ W := fun y hy => hsub (show f y ≤ s' by linarith)
  have hLimage : (Subtype.val : Wo → Z) '' {x : Wo | fW x = s} = {x | f x = s} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hlevW y hy⟩, hy, rfl⟩
  have hLcpt : IsCompact {x : Wo | fW x = s} := by
    rw [Subtype.isCompact_iff, hLimage]
    exact hcpt.of_isClosed_subset (isClosed_eq hf continuous_const) fun x hx => by
      change f x = s at hx
      change f x ≤ s'
      linarith
  have hLconn : IsConnected {x : Wo | fW x = s} := by
    have hc : IsConnected {x : Z | f x = s} := by
      rw [← hbd]
      exact isConnected_diskSphere_two.image φ hφ.continuousOn
    have hind : Topology.IsInducing (Subtype.val : Wo → Z) := Topology.IsInducing.subtypeVal
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy⟩ := hc.nonempty
      exact ⟨⟨y, hlevW y hy⟩, hy⟩
    · apply hind.isPreconnected_image.mp
      rw [hLimage]
      exact hc.isPreconnected
  obtain ⟨Dc⟩ := DifferentialGeometry.Topology.Manifold.OneManifold.nonempty_circle_diffeomorph_regularFiber
    fW s hfWs hLreg (by simp [hE]) hLcpt hLconn
  let L := {x : Wo // fW x = s}
  let _ : ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) L :=
    DifferentialGeometry.Topology.Manifold.regularFiberChartedSpace fW s hfWs hLreg
  let D' := AddCircle.diffeomorphCircle.trans Dc
  have hss : 0 ≤ s' - s := by linarith
  let c₁ : L → S := fun x => ⟨(x.1, √(s' - s)), by
    rw [hGdef]
    have hx : f x.1 = s := x.2
    rw [hx, Real.sq_sqrt hss]
    ring⟩
  have hc₁ : ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
      𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) ∞ c₁ :=
    (DifferentialGeometry.Topology.Manifold.contMDiff_regularFiber_iff G s' hG hGreg c₁).mpr
      ((DifferentialGeometry.Topology.Manifold.contMDiff_regularFiberInclusion fW s hfWs
        hLreg).prodMk contMDiff_const)
  have hc₁i : Injective c₁ := fun a b h =>
    Subtype.ext (congrArg (fun p : S => p.1.1) h)
  have hLval := DifferentialGeometry.Topology.Manifold.contMDiff_regularFiberInclusion fW s hfWs hLreg
  have hSval := DifferentialGeometry.Topology.Manifold.contMDiff_regularFiberInclusion G s' hG hGreg
  have hc₁inj : ∀ x : L, Injective (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
      𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) c₁ x) := by
    intro x v w hvw
    have hcomp : HasMFDerivAt 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
        (I.prod 𝓘(ℝ, ℝ)) (fun y : L => ((y.1 : Wo), √(s' - s))) x
        ((mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) (I.prod 𝓘(ℝ, ℝ))
          (Subtype.val : S → Wo × ℝ) (c₁ x)).comp
          (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
            𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) c₁ x)) :=
      (hSval.mdifferentiableAt (by simp)).hasMFDerivAt.comp x
        (hc₁.mdifferentiableAt (by simp)).hasMFDerivAt
    have hprod : HasMFDerivAt 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
        (I.prod 𝓘(ℝ, ℝ)) (fun y : L => ((y.1 : Wo), √(s' - s))) x
        ((mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) I
          (Subtype.val : L → Wo) x).prod 0) :=
      (hLval.mdifferentiableAt (by simp)).hasMFDerivAt.prodMk (hasMFDerivAt_const _ _)
    have heq := hcomp.mfderiv.symm.trans hprod.mfderiv
    have key : ∀ u, (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ)
        (I.prod 𝓘(ℝ, ℝ)) (Subtype.val : S → Wo × ℝ) (c₁ x))
          (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
            𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) c₁ x u) =
        ((mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) I
          (Subtype.val : L → Wo) x).prod 0) u := by
      intro u
      rw [← heq]
      rfl
    have h4 := (key v).symm.trans ((congrArg _ hvw).trans (key w))
    have h3 := congrArg Prod.fst h4
    simp only [ContinuousLinearMap.prod_apply] at h3
    exact DifferentialGeometry.Topology.Manifold.mfderiv_regularFiberInclusion_injective fW s hfWs
      hLreg x h3
  let γ : AddCircle (1 : ℝ) → SphereTwo := Ψ ∘ c₁ ∘ D'
  have hγc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ := Ψ.contMDiff.comp (hc₁.comp D'.contMDiff)
  have hγi : Injective γ := Ψ.injective.comp (hc₁i.comp D'.injective)
  have hγinj : ∀ x, Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ x) := by
    intro x
    have h3 : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 2) γ x
        ((mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) (𝓡 2) Ψ
          (c₁ (D' x))).comp
          ((mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
            𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) c₁ (D' x)).comp
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) D' x))) :=
      (Ψ.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt.comp x
        ((hc₁.mdifferentiableAt (by simp)).hasMFDerivAt.comp x
          (D'.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt)
    rw [h3.mfderiv, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
    exact (Ψ.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      ((hc₁inj (D' x)).comp (D'.mfderivToContinuousLinearEquiv (by simp) x).injective)
  have hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ :=
    ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hγc hγinj,
      (hγc.continuous.isClosedEmbedding hγi).isEmbedding⟩
  ------------------------------------------------------------------ step 4: Schoenflies on `S²`
  obtain ⟨b₀, b₁, hb₀, hb₁, hb₀C, hb₁C, hcov', hint'⟩ :=
    Handle.exists_two_smooth_disks_sphere_of_circle hγ
  ------------------------------------------------------------------ step 5: the side of `D_s`
  have hφW : ∀ x, φ x ∈ W := fun x => hsub (show f (φ x) ≤ s' by linarith [hφle x])
  let hφt : Disk 2 → ℝ := fun x => √(s' - f (φ x))
  have hφpos : ∀ x, 0 < hφt x := fun x => Real.sqrt_pos.mpr (by linarith [hφle x])
  let jφ : Disk 2 → S := fun x => ⟨(⟨φ x, hφW x⟩, hφt x), by
    rw [hGdef]
    change f (φ x) + √(s' - f (φ x)) ^ 2 = s'
    rw [Real.sq_sqrt (by linarith [hφle x])]
    ring⟩
  have hjφc : Continuous jφ :=
    ((hφ.subtype_mk hφW).prodMk (Real.continuous_sqrt.comp (continuous_const.sub
      (hf.comp hφ)))).subtype_mk _
  have hjφi : Injective jφ := fun a b h => hφ' (congrArg (fun p : S => (p.1.1 : Z)) h)
  have hφs : ∀ z ∈ diskSphere 2, f (φ z) = s := fun z hz => by
    have h : φ z ∈ φ '' diskSphere 2 := mem_image_of_mem _ hz
    rw [hbd] at h
    exact h
  have hγrange : range γ = Ψ '' (jφ '' diskSphere 2) := by
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      have hy : f (D' x).1.1 = s := (D' x).2
      have hmem : ((D' x).1.1 : Z) ∈ φ '' diskSphere 2 := by rw [hbd]; exact hy
      obtain ⟨z, hz, hzy⟩ := hmem
      refine ⟨jφ z, ⟨z, hz, rfl⟩, ?_⟩
      change Ψ (jφ z) = Ψ (c₁ (D' x))
      congr 1
      apply Subtype.ext
      refine Prod.ext (Subtype.ext hzy) ?_
      change √(s' - f (φ z)) = √(s' - s)
      rw [hzy, hy]
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      let y : L := ⟨⟨φ z, hφW z⟩, hφs z hz⟩
      refine ⟨D'.symm y, ?_⟩
      change Ψ (c₁ (D' (D'.symm y))) = Ψ (jφ z)
      rw [D'.apply_symm_apply]
      congr 1
      apply Subtype.ext
      refine Prod.ext rfl ?_
      change √(s' - s) = √(s' - f (φ z))
      rw [hφs z hz]
  have hP₀ : jφ '' diskInterior 2 = {p : S | f p.1.1 < s ∧ 0 < p.1.2} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, hφpos x⟩
      change f (φ x) < s
      rcases lt_or_eq_of_le (hφle x) with h | h
      · exact h
      · exfalso
        have hm : φ x ∈ φ '' diskSphere 2 := by rw [hbd]; exact h
        obtain ⟨z, hz, hzx⟩ := hm
        rw [hφ' hzx] at hz
        exact Set.disjoint_left.mp (disjoint_diskSphere_diskInterior 2) hz hx
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hx⟩ : (p.1.1 : Z) ∈ range φ := by rw [hrange]; exact h1.le
      have hxi : x ∈ diskInterior 2 := by
        have hx' : x ∈ diskSphere 2 ∪ diskInterior 2 := by
          rw [diskSphere_union_diskInterior]
          trivial
        rcases hx' with h | h
        · exfalso
          have := hφs x h
          rw [hx] at this
          exact absurd this (ne_of_lt h1)
        · exact h
      refine ⟨x, hxi, ?_⟩
      apply Subtype.ext
      refine Prod.ext (Subtype.ext hx) ?_
      have hp : f p.1.1 + p.1.2 ^ 2 = s' := p.2
      change √(s' - f (φ x)) = p.1.2
      rw [hx]
      have hsq : s' - f p.1.1 = p.1.2 ^ 2 := by linarith
      rw [hsq, Real.sqrt_sq h2.le]
  have hPopen : IsOpen (Ψ '' (jφ '' diskInterior 2)) := by
    have hcS : Continuous (fun p : S => f p.1.1) :=
      hf.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    have hopen : IsOpen {p : S | f p.1.1 < s ∧ 0 < p.1.2} :=
      (isOpen_lt hcS continuous_const).inter
        (isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val))
    rw [hP₀]
    exact Ψ.toHomeomorph.isOpenMap _ hopen
  have hPconn : IsConnected (Ψ '' (jφ '' diskInterior 2)) := by
    rw [← image_comp]
    exact (isConnected_diskInterior 2).image _ (Ψ.continuous.comp hjφc).continuousOn
  have hPC : Disjoint (Ψ '' (jφ '' diskInterior 2)) (range γ) := by
    rw [hγrange]
    exact (disjoint_image_iff Ψ.injective).mpr
      ((disjoint_image_iff hjφi).mpr (disjoint_diskSphere_diskInterior 2).symm)
  have hPC_eq : Ψ '' (jφ '' diskInterior 2) ∪ range γ = range (Ψ ∘ jφ) := by
    rw [hγrange, ← image_union, ← image_union, union_comm (diskInterior 2),
      diskSphere_union_diskInterior, image_univ, range_comp]
  have hKc : IsClosed (Ψ '' (jφ '' diskInterior 2) ∪ range γ) := by
    rw [hPC_eq]
    exact (isCompact_range (Ψ.continuous.comp hjφc)).isClosed
  have hside := union_eq_range_or_range (n := 2) hb₀.isEmbedding.continuous
    hb₀.isEmbedding.injective hb₁.isEmbedding.continuous hb₁.isEmbedding.injective hb₀C hb₁C
    hcov' hint' hPopen hPconn hPC hKc
  obtain ⟨bsel, hbsel, hselC, hsel⟩ : ∃ bsel : ClosedCell 2 → SphereTwo,
      Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ bsel ∧
        range (bsel ∘ cellBoundaryInclusion 2) = range γ ∧ range bsel = range (Ψ ∘ jφ) := by
    rcases hside with h | h
    · exact ⟨b₀, hb₀, hb₀C, h.symm.trans hPC_eq⟩
    · exact ⟨b₁, hb₁, hb₁C, h.symm.trans hPC_eq⟩
  ------------------------------------------------------------------ step 6: back to `Z`
  let π : S → Z := fun p => (p.1.1 : Z)
  have hπ : ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) I ∞ π :=
    contMDiff_subtype_val.comp (contMDiff_fst.comp hSval)
  have hπinj : ∀ q : S, 0 < q.1.2 →
      Injective (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) I π q) := by
    intro q hq
    have hSd : MDifferentiableAt 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ)
        (I.prod 𝓘(ℝ, ℝ)) (Subtype.val : S → Wo × ℝ) q := hSval.mdifferentiableAt (by simp)
    have hπd := (DifferentialGeometry.hasMFDerivAt_subtype_val (I := I) Wo q.1.1).comp q
      ((hasMFDerivAt_fst q.1).comp q hSd.hasMFDerivAt)
    obtain ⟨Lq, hLq, hLqv⟩ := exists_hasMFDerivAt_roundedHeight hfWo q.1
    have hGc := hLq.comp q hSd.hasMFDerivAt
    have hconst : (G ∘ (Subtype.val : S → Wo × ℝ)) = fun _ => s' := funext fun r => r.2
    have hzero : ∀ u, Lq (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ)
        (I.prod 𝓘(ℝ, ℝ)) (Subtype.val : S → Wo × ℝ) q u) = 0 := by
      intro u
      have h1 := hGc.mfderiv
      rw [hconst, mfderiv_const] at h1
      have h2 := congrArg (fun T => T u) h1
      exact h2.symm
    have hπeq : HasMFDerivAt 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) I π q _ :=
      hπd
    rw [hπeq.mfderiv, injective_iff_map_eq_zero]
    intro u hu
    let w : E × ℝ := mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ)
      (I.prod 𝓘(ℝ, ℝ)) (Subtype.val : S → Wo × ℝ) q u
    have hu1 : w.1 = 0 := hu
    have hu2 : Lq w = 0 := hzero u
    rw [hLqv] at hu2
    have hz : mvfderiv (I := I) f (q.1.1 : Z) w.1 = 0 := by
      have h0 : (w.1 : TangentSpace I (q.1.1 : Z)) = 0 := hu1
      rw [h0]
      exact map_zero _
    rw [hz, zero_add] at hu2
    have hu3 : w.2 = 0 := by
      rcases mul_eq_zero.mp hu2 with h | h
      · exfalso
        linarith
      · exact h
    have hw0 : w = 0 := Prod.ext hu1 hu3
    apply DifferentialGeometry.Topology.Manifold.mfderiv_regularFiberInclusion_injective G s' hG
      hGreg q
    change w = _
    rw [hw0, map_zero]
    rfl
  let b : ClosedCell 2 → Z := (π ∘ Ψ.symm) ∘ bsel
  have hval : ∀ x : Disk 2, (π ∘ Ψ.symm) ((Ψ ∘ jφ) x) = φ x := fun x => by
    simp only [comp_apply, Diffeomorph.symm_apply_apply]
    rfl
  have hrangeb : range b = range φ := by
    rw [range_comp, hsel, ← range_comp]
    exact congrArg range (funext hval)
  have hbdb : range (b ∘ cellBoundaryInclusion 2) = φ '' diskSphere 2 := by
    have hcomp : b ∘ cellBoundaryInclusion 2 = (π ∘ Ψ.symm) ∘ (bsel ∘ cellBoundaryInclusion 2) :=
      rfl
    rw [hcomp, range_comp, hselC, hγrange, image_image, image_image]
    exact image_congr fun x _ => hval x
  have hbi : Injective b := by
    intro x y hxy
    obtain ⟨u, hu⟩ : bsel x ∈ range (Ψ ∘ jφ) := hsel ▸ mem_range_self x
    obtain ⟨v, hv⟩ : bsel y ∈ range (Ψ ∘ jφ) := hsel ▸ mem_range_self y
    have h1 : b x = φ u := by
      change (π ∘ Ψ.symm) (bsel x) = φ u
      rw [← hu, hval]
    have h2 : b y = φ v := by
      change (π ∘ Ψ.symm) (bsel y) = φ v
      rw [← hv, hval]
    have huv : u = v := hφ' (h1.symm.trans (hxy.trans h2))
    apply hbsel.isEmbedding.injective
    rw [← hu, ← hv, huv]
  have hbc : Continuous b :=
    (hπ.continuous.comp Ψ.symm.continuous).comp hbsel.isEmbedding.continuous
  have hsm : ContMDiff (𝓡 2) I ∞ (π ∘ Ψ.symm) := hπ.comp Ψ.symm.contMDiff
  have hloc : IsLocalDiffeomorphOn (𝓡 2) I ∞ (π ∘ Ψ.symm) (range bsel) := by
    rintro ⟨y, hy⟩
    rw [hsel] at hy
    obtain ⟨x, rfl⟩ := hy
    have hcompd : HasMFDerivAt (𝓡 2) I (π ∘ Ψ.symm) ((Ψ ∘ jφ) x)
        ((mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) I π
          (Ψ.symm ((Ψ ∘ jφ) x))).comp
          (mfderiv (𝓡 2) 𝓘(ℝ, Fin (Module.finrank ℝ (E × ℝ) - Module.finrank ℝ ℝ) → ℝ) Ψ.symm
            ((Ψ ∘ jφ) x))) :=
      (hπ.mdifferentiableAt (by simp)).hasMFDerivAt.comp _
        (Ψ.symm.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
    have hq : Ψ.symm ((Ψ ∘ jφ) x) = jφ x := Ψ.symm_apply_apply (jφ x)
    have hinj : Injective (mfderiv (𝓡 2) I (π ∘ Ψ.symm) ((Ψ ∘ jφ) x)) := by
      rw [hcompd.mfderiv, ContinuousLinearMap.coe_comp]
      refine Injective.comp (hπinj _ ?_)
        (Ψ.symm.mfderivToContinuousLinearEquiv (by simp) _).injective
      rw [hq]
      exact hφpos x
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = Module.finrank ℝ E := by
      simp [hE]
    let D := mfderiv (𝓡 2) I (π ∘ Ψ.symm) ((Ψ ∘ jφ) x)
    let A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] E :=
      (D.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
    exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_hasMFDerivAt_equiv _ hsm
      _ A ((hsm.mdifferentiableAt (by simp)).hasMFDerivAt)
  have himm : Manifold.IsImmersion (𝓡∂ 2) I ∞ b :=
    Manifold.IsImmersion.isLocalDiffeomorphOn_comp_of_ne_zero hbsel.isImmersion hloc (by simp)
  refine ⟨b, ⟨himm, (hbc.isClosedEmbedding hbi).isEmbedding⟩, ?_, ?_⟩
  · rw [hrangeb, hrange]
  · rw [hbdb, hbd]

end DifferentialGeometry.Topology.Surface
