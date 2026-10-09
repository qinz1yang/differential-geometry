import DifferentialGeometry.Topology.Ehresmann.BallTrivialization

/-!
# LC83, kernel: a submersion to the plane with two enclosures is a trivial bundle

Blueprint 207A, LC83 (`prop:collapse-two-stratum-local`, A:25167–25199). Abstract form: `η` is a
smooth submersion to `ℝ²` on an open set `W` of a smooth manifold, `η(p) = 0`, the part of `W` where
`‖η‖ < r` lies in a compact `K ⊆ W` (first enclosure), and every point of the zero fibre is joined
to `p` inside `{y ∈ W | ‖η y‖ < ρ}`, `ρ < r` (what the second enclosure gives on a length space).

* `diskPreimageOpens`, `diskPreimageMap`: the bundle domain `W ∩ η⁻¹ B(0, r)` and `η` on it, as a
  map to the open disk `planeBallOpens r`.
* `contMDiff_diskPreimageMap`, `mfderiv_diskPreimageMap`, `surjective_mfderiv_diskPreimageMap`,
  `isProperMap_diskPreimageMap`.
* `exists_trivial_proper_submersion_of_enclosure` (LC83 kernel): smooth, submersion, proper,
  surjective, every fibre compact and connected, and trivial over every `B(0, R)`, `R < r`, with
  fibre the zero fibre (a boundaryless manifold modelled on `Fin (dim − 2) → ℝ`).

Not proved here: "each fibre is a circle" (classification of compact connected 1-manifolds, lane
W4-FCb); triviality over the whole open disk `B(0, r)` (only every smaller disk).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}

/-- The bundle domain `W ∩ η⁻¹ B(0, r)` of LC83 as an open set. -/
def diskPreimageOpens (W : Set M) (hW : IsOpen W) (η : M → ℝ²) (hη : ContinuousOn η W) (r : ℝ) :
    TopologicalSpace.Opens M :=
  ⟨W ∩ η ⁻¹' ball 0 r, hη.isOpen_inter_preimage hW isOpen_ball⟩

/-- `η` restricted to the bundle domain, as a map to the open disk `B(0, r)`. -/
def diskPreimageMap (W : Set M) (hW : IsOpen W) (η : M → ℝ²) (hη : ContinuousOn η W) (r : ℝ) :
    diskPreimageOpens W hW η hη r → planeBallOpens r :=
  fun x => ⟨η x, mem_planeBallOpens_iff.mpr (by
    have h := x.2.2
    rwa [mem_preimage, mem_ball, dist_zero_right] at h)⟩

theorem diskPreimageMap_coe (W : Set M) (hW : IsOpen W) (η : M → ℝ²) (hη : ContinuousOn η W)
    (r : ℝ) (x : diskPreimageOpens W hW η hη r) :
    (diskPreimageMap W hW η hη r x : ℝ²) = η x :=
  rfl

theorem contMDiff_diskPreimageMap {W : Set M} (hW : IsOpen W) {η : M → ℝ²}
    (hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η W) (r : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ²) ∞ (diskPreimageMap W hW η hη.continuousOn r) := by
  apply (ContMDiff.subtypeVal_comp_iff (planeBallOpens r) _).mp
  exact hη.comp_contMDiff contMDiff_subtype_val (fun x => x.2.1)

theorem mfderiv_diskPreimageMap {W : Set M} (hW : IsOpen W) {η : M → ℝ²}
    (hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η W) (r : ℝ) (x : diskPreimageOpens W hW η hη.continuousOn r) :
    mfderiv I 𝓘(ℝ, ℝ²) (diskPreimageMap W hW η hη.continuousOn r) x =
      mfderiv I 𝓘(ℝ, ℝ²) η x.1 := by
  set f := diskPreimageMap W hW η hη.continuousOn r
  have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ²) f x :=
    ((contMDiff_diskPreimageMap hW hη r) x).mdifferentiableAt (by simp)
  have hηd : MDifferentiableAt I 𝓘(ℝ, ℝ²) η x.1 :=
    ((hη x.1 x.2.1).contMDiffAt (hW.mem_nhds x.2.1)).mdifferentiableAt (by simp)
  have h1 : HasMFDerivAt I 𝓘(ℝ, ℝ²) (Subtype.val ∘ f) x
      ((ContinuousLinearMap.id ℝ ℝ²).comp (mfderiv I 𝓘(ℝ, ℝ²) f x)) :=
    (DifferentialGeometry.hasMFDerivAt_subtype_val (I := 𝓘(ℝ, ℝ²)) (planeBallOpens r)
      (f x)).comp x hfd.hasMFDerivAt
  have h2 : HasMFDerivAt I 𝓘(ℝ, ℝ²) (η ∘ Subtype.val) x
      ((mfderiv I 𝓘(ℝ, ℝ²) η x.1).comp (ContinuousLinearMap.id ℝ E)) :=
    hηd.hasMFDerivAt.comp x (DifferentialGeometry.hasMFDerivAt_subtype_val (I := I) _ x)
  have h1' : HasMFDerivAt I 𝓘(ℝ, ℝ²) (η ∘ Subtype.val) x
      ((ContinuousLinearMap.id ℝ ℝ²).comp (mfderiv I 𝓘(ℝ, ℝ²) f x)) := h1
  have := hasMFDerivAt_unique h1' h2
  ext v
  exact congrArg (fun L : E →L[ℝ] ℝ² => L v) this


theorem surjective_mfderiv_diskPreimageMap {W : Set M} (hW : IsOpen W)
    {η : M → ℝ²} (hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η W)
    (hreg : ∀ x ∈ W, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x)) (r : ℝ)
    (x : diskPreimageOpens W hW η hη.continuousOn r) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ²) (diskPreimageMap W hW η hη.continuousOn r) x) := by
  rw [mfderiv_diskPreimageMap hW hη r x]
  exact hreg x.1 x.2.1

theorem continuous_diskPreimageMap {W : Set M} (hW : IsOpen W) {η : M → ℝ²}
    (hη : ContinuousOn η W) (r : ℝ) : Continuous (diskPreimageMap W hW η hη r) :=
  (hη.comp_continuous continuous_subtype_val (fun x => x.2.1)).subtype_mk _

theorem isProperMap_diskPreimageMap [T2Space M] {W : Set M} (hW : IsOpen W) {η : M → ℝ²}
    (hη : ContinuousOn η W) {r : ℝ} {K : Set M} (hK : IsCompact K) (hKW : K ⊆ W)
    (hencl : ∀ x ∈ W, ‖η x‖ < r → x ∈ K) : IsProperMap (diskPreimageMap W hW η hη r) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_diskPreimageMap hW hη r, fun C hC => ?_⟩
  set f := diskPreimageMap W hW η hη r
  have hC' : IsCompact (Subtype.val '' C : Set ℝ²) := hC.image continuous_subtype_val
  have himage : Subtype.val '' (f ⁻¹' C) = K ∩ η ⁻¹' (Subtype.val '' C) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hnorm : ‖η u.1‖ < r := by
        have h := u.2.2
        rwa [mem_preimage, mem_ball, dist_zero_right] at h
      exact ⟨hencl u.1 u.2.1 hnorm, f u, hu, rfl⟩
    · rintro ⟨hxK, c, hc, hcx⟩
      have hxb : η x ∈ ball (0 : ℝ²) r := by
        rw [← hcx]
        have := c.2
        rwa [mem_planeBallOpens_iff, ← dist_zero_right, ← mem_ball] at this
      refine ⟨⟨x, hKW hxK, hxb⟩, ?_, rfl⟩
      have hfx : f ⟨x, hKW hxK, hxb⟩ = c := Subtype.ext hcx.symm
      rw [mem_preimage, hfx]
      exact hc
  rw [Subtype.isCompact_iff, himage]
  exact hK.of_isClosed_subset ((hη.mono hKW).preimage_isClosed_of_isClosed hK.isClosed
    hC'.isClosed) inter_subset_left

theorem sigmaCompactSpace_of_isProperMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SigmaCompactSpace Y] {f : X → Y} (hf : IsProperMap f) : SigmaCompactSpace X :=
  ⟨⟨fun n => f ⁻¹' compactCovering Y n,
    fun n => hf.isCompact_preimage (isCompact_compactCovering Y n), by
      rw [← preimage_iUnion, iUnion_compactCovering, preimage_univ]⟩⟩


/-- **LC83, kernel.** Let `η` be a smooth submersion to `ℝ²` on an open set `W` of a smooth manifold,
with `η(p) = 0`, such that the part of `W` where `‖η‖ < r` lies in a compact `K ⊆ W`, and every
point of the zero fibre is joined to `p` inside `{y ∈ W | ‖η y‖ < ρ}` with `ρ < r`. Then
`η : W ∩ η⁻¹ B(0, r) → B(0, r)` is a proper surjective submersion with compact connected fibres,
and it is trivial over every `B(0, R)`, `R < r`, with fibre the zero fibre. -/
theorem exists_trivial_proper_submersion_of_enclosure [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    {W : Set M} (hW : IsOpen W) {η : M → ℝ²} (hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η W)
    (hreg : ∀ x ∈ W, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x)) {r : ℝ}
    {K : Set M} (hK : IsCompact K) (hKW : K ⊆ W) (hencl : ∀ x ∈ W, ‖η x‖ < r → x ∈ K)
    {p : M} (hpW : p ∈ W) (hp : η p = 0) {ρ : ℝ} (hρr : ρ < r)
    (hjoin : ∀ x ∈ W, η x = 0 → JoinedIn {y | y ∈ W ∧ ‖η y‖ < ρ} x p) :
    let f := diskPreimageMap W hW η hη.continuousOn r
    ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧ (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧
      Surjective f ∧ (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
      ∀ R (hR : 0 < R) (hRr : R < r),
        let y₀ : planeBallOpens r := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
        let _ := regularFiberChartedSpace f y₀ (contMDiff_diskPreimageMap hW hη r)
          (fun x _ ↦ surjective_mfderiv_diskPreimageMap hW hη hreg r x)
        let U : TopologicalSpace.Opens (diskPreimageOpens W hW η hη.continuousOn r) :=
          ⟨f ⁻¹' planeBallInner r R,
            (planeBallInner r R).isOpen.preimage (continuous_diskPreimageMap hW _ r)⟩
        ∃ (hy : y₀ ∈ planeBallInner r R) (Θ : Diffeomorph
            (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
            ({x // f x = y₀} × planeBallInner r R) U ∞),
          (∀ q, f (Θ q).1 = q.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1) := by
  intro f
  have hf : ContMDiff I 𝓘(ℝ, ℝ²) ∞ f := contMDiff_diskPreimageMap hW hη r
  have hsub : ∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x) :=
    surjective_mfderiv_diskPreimageMap hW hη hreg r
  have hprop : IsProperMap f := isProperMap_diskPreimageMap hW hη.continuousOn hK hKW hencl
  have : LocallyCompactSpace (planeBallOpens r) := (planeBallOpens r).isOpen.locallyCompactSpace
  have : SigmaCompactSpace (diskPreimageOpens W hW η hη.continuousOn r) :=
    sigmaCompactSpace_of_isProperMap hprop
  have htriv : ∀ R (hR : 0 < R) (hRr : R < r),
      let y₀ : planeBallOpens r := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
      let _ := regularFiberChartedSpace f y₀ hf (fun x _ ↦ hsub x)
      let U : TopologicalSpace.Opens (diskPreimageOpens W hW η hη.continuousOn r) :=
        ⟨f ⁻¹' planeBallInner r R, (planeBallInner r R).isOpen.preimage hf.continuous⟩
      ∃ (hy : y₀ ∈ planeBallInner r R) (Θ : Diffeomorph
          (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
          ({x // f x = y₀} × planeBallInner r R) U ∞),
        (∀ q, f (Θ q).1 = q.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1) :=
    fun R hR hRr => exists_trivialization_over_planeBall_of_proper f hf hprop hsub hR hRr
  have hpS := (hjoin p hpW hp).mem
  have hρ : 0 < ρ := by
    have h := hpS.1.2
    rwa [hp, norm_zero] at h
  have hr : 0 < r := hρ.trans hρr
  have hpU : p ∈ diskPreimageOpens W hW η hη.continuousOn r := by
    refine ⟨hpW, ?_⟩
    rw [mem_preimage, hp]
    exact mem_ball_self hr
  set y₀ : planeBallOpens r := ⟨0, zero_mem_planeBallOpens hr⟩ with hy₀def
  let _ := regularFiberChartedSpace f y₀ hf (fun x _ ↦ hsub x)
  have hfp : f ⟨p, hpU⟩ = y₀ := Subtype.ext hp
  set p₀ : {x // f x = y₀} := ⟨⟨p, hpU⟩, hfp⟩
  set R₁ : ℝ := max ρ (r / 2)
  have hR₁ : 0 < R₁ := lt_max_of_lt_left hρ
  have hR₁r : R₁ < r := max_lt hρr (by linarith)
  have hconn0 : IsPreconnected (univ : Set {x // f x = y₀}) := by
    obtain ⟨hy, Θ, -, hid⟩ := htriv R₁ hR₁ hR₁r
    refine isPreconnected_of_forall p₀ fun a _ => ?_
    have ha : η a.1.1 = 0 := congrArg Subtype.val a.2
    obtain ⟨γ, hγ⟩ := hjoin a.1.1 a.1.2.1 ha
    have hγU : ∀ t, γ t ∈ diskPreimageOpens W hW η hη.continuousOn r := fun t =>
      ⟨(hγ t).1, by
        rw [mem_preimage, mem_ball, dist_zero_right]
        exact (hγ t).2.trans hρr⟩
    have hγQ : ∀ t, f ⟨γ t, hγU t⟩ ∈ planeBallInner r R₁ := fun t =>
      mem_planeBallInner_iff.mpr ((hγ t).2.trans_le (le_max_left _ _))
    let γU : unitInterval → {u // f u ∈ planeBallInner r R₁} := fun t => ⟨⟨γ t, hγU t⟩, hγQ t⟩
    have hγUc : Continuous γU := (γ.continuous.subtype_mk _).subtype_mk _
    let c : unitInterval → {x // f x = y₀} := fun t => (Θ.symm (γU t)).1
    have hc : Continuous c := continuous_fst.comp (Θ.symm.continuous.comp hγUc)
    have hend : ∀ (b : {x // f x = y₀}) (t : unitInterval), (γ t : M) = b.1.1 → c t = b := by
      intro b t hbt
      have hΘ : Θ (b, ⟨_, hy⟩) = γU t := by
        apply Subtype.ext
        rw [hid b]
        exact Subtype.ext hbt.symm
      change (Θ.symm (γU t)).1 = b
      rw [← hΘ, Diffeomorph.symm_apply_apply]
    exact ⟨range c, subset_univ _, ⟨1, hend p₀ 1 (by simp [p₀])⟩,
      ⟨0, hend a 0 (by simp)⟩, isPreconnected_range hc⟩
  have : ConnectedSpace {x // f x = y₀} :=
    { isPreconnected_univ := hconn0, toNonempty := ⟨p₀⟩ }
  have hfib : ∀ z : planeBallOpens r, (f ⁻¹' {z}).Nonempty ∧ IsConnected (f ⁻¹' {z}) := by
    intro z
    have hz := mem_planeBallOpens_iff.mp z.2
    have hRz : 0 < (‖(z : ℝ²)‖ + r) / 2 := by
      have := norm_nonneg (z : ℝ²)
      linarith
    have hRzr : (‖(z : ℝ²)‖ + r) / 2 < r := by linarith
    obtain ⟨hy, Θ, hover, -⟩ := htriv _ hRz hRzr
    have hzQ : z ∈ planeBallInner r ((‖(z : ℝ²)‖ + r) / 2) :=
      mem_planeBallInner_iff.mpr (by linarith)
    let φ : {x // f x = y₀} → diskPreimageOpens W hW η hη.continuousOn r :=
      fun a => (Θ (a, ⟨z, hzQ⟩)).1
    have hφ : Continuous φ :=
      continuous_subtype_val.comp (Θ.continuous.comp (Continuous.prodMk_left _))
    have heq : f ⁻¹' {z} = range φ := by
      ext u
      constructor
      · intro hu
        have hu' : f u = z := hu
        have huQ : f u ∈ planeBallInner r ((‖(z : ℝ²)‖ + r) / 2) := hu' ▸ hzQ
        let uu : {u // f u ∈ planeBallInner r ((‖(z : ℝ²)‖ + r) / 2)} := ⟨u, huQ⟩
        have hq2 : (Θ.symm uu).2 = ⟨z, hzQ⟩ := by
          apply Subtype.ext
          rw [← hover, Diffeomorph.apply_symm_apply]
          exact hu'
        refine ⟨(Θ.symm uu).1, ?_⟩
        change (Θ ((Θ.symm uu).1, ⟨z, hzQ⟩)).1 = u
        rw [← hq2, Prod.mk.eta, Diffeomorph.apply_symm_apply]
      · rintro ⟨a, rfl⟩
        exact hover (a, ⟨z, hzQ⟩)
    rw [heq]
    exact ⟨range_nonempty φ, isConnected_range hφ⟩
  refine ⟨hf, hsub, hprop, fun z => ?_, fun z => ⟨hprop.isCompact_preimage isCompact_singleton,
    (hfib z).2⟩, htriv⟩
  obtain ⟨u, hu⟩ := (hfib z).1
  exact ⟨u, hu⟩

end DifferentialGeometry.Geometry.Collapse
