import DifferentialGeometry.Geometry.Collapse.SublevelCore.FieldBandSmooth
import DifferentialGeometry.Geometry.Collapse.SublevelCore.DistanceBallIsotopy
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenGraphStraightening
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# LC60: smooth open-distance-ball comparison with small displacement

Blueprint LC60 (`master207A.tex:23408`). In the LC32–LC34 setting (PC Riemannian manifold, LC30
radial function `η` with `|η - d_p| < e`, `0 ≤ ε < 1/4`, `e < 1/40`, `ρ ∈ [1/5, 2]`) there is a
diffeomorphism of OPEN sets `J_ρ : int {η ≤ ρ} → B(p, ρ)` (ambient smooth structure), equal to
the identity where `η ≤ ρ - 2e`, moving points by less than `3e / (1 - ε)`; it fixes `p`.

Proof (blueprint A:23430–23452), with the SAME flow `Φ` and height `h_ρ` of LC33–LC34:
* `exists_openBand_levelChart`: the level `L = η⁻¹(1)` carries the regular-level structure of
  the Morse library and `y ↦ (Φ (1 - η y) y, η y)` is a partial diffeomorphism from the OPEN band
  `{1/8 < η < 3}` onto `L × (1/8, 3)` with inverse `(x, u) ↦ Φ (u - 1) x` (the factor property of
  the level structure gives the smoothness of the first component);
* `dist_flow_le_of_speed_bound`: a flow segment inside the band of parameter length `|s|` has
  length at most `C |s|` when the velocity has speed `≤ C` (here `C = (1 - ε)⁻¹`);
* `exists_open_distance_ball_diffeomorph`: LC59 (`exists_openGraph_straightening`) on `L` with
  heights `ρ` and `h_ρ`, `c = ρ - 2e`, conjugated by the chart and extended by the identity below
  the band; the inverse function theorem is not needed again (injective local diffeomorphism,
  `IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn`).

The blueprint hypothesis `0 < e` follows from `|η - d_p| < e` and is dropped. The `E H M : Type`
restriction is that of the Morse library.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Morse

section Chart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The open-band chart with the level given as an arbitrary set equal to the regular level
`f⁻¹(1)` of a globally smooth `f` that agrees with `η` on the band. -/
private theorem openBandChart_aux {m : ℕ} (hdim : Module.finrank ℝ E = m + 1) {f η : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hreg1 : ∀ x, f x = 1 → ¬ IsCriticalPointAt I f x)
    (hη : Continuous η) {W : Set M} (hW : IsOpen W) (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    {a b : ℝ} (ha1 : a ≤ 1) (h1b : 1 ≤ b) (hbandW : η ⁻¹' Icc a b ⊆ W)
    (hfη : ∀ x, η x ∈ Icc a b → f x = η x)
    {Φ : ℝ → M → M} (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hval : ∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s)
    {L : Set M} (hL : {x | f x = 1} = L) (hLη : ∀ x ∈ L, η x = 1) (x₀ : M) (hx₀ : x₀ ∈ L) :
    ∃ cs : ChartedSpace (MorseModel m) L,
      letI := cs
      IsManifold 𝓘(ℝ, MorseModel m) ∞ L ∧
      ∃ bc : PartialDiffeomorph I (𝓘(ℝ, MorseModel m).prod 𝓘(ℝ, ℝ)) M (L × ℝ) ∞,
        bc.source = {y | a < η y ∧ η y < b} ∧ bc.target = {z | a < z.2 ∧ z.2 < b} ∧
        (∀ y ∈ bc.source, ((bc y).1 : M) = Φ (1 - η y) y ∧ (bc y).2 = η y) ∧
        ∀ z, bc.symm z = Φ (z.2 - 1) z.1 := by
  subst hL
  let e : E ≃L[ℝ] MorseModel (m + 1) :=
    ContinuousLinearEquiv.ofFinrankEq (hdim.trans (Module.finrank_fin_fun ℝ).symm)
  let J := I.transContinuousLinearEquiv e
  have hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f := (e.contMDiff_transContinuousLinearEquiv_left).mpr hf
  have hregc : ∀ x, f x = 1 → ¬ IsCriticalPointAt J f x := fun x hx hcr =>
    hreg1 x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff I e f x).mp hcr)
  let T : M ≃ₘ⟮I, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e
  have hΦJ : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ (fun q : ℝ × M => Φ q.1 q.2) :=
    (e.contMDiff_transContinuousLinearEquiv_right.mpr hΦc).comp
      (contMDiff_fst.prodMk (T.symm.contMDiff.comp contMDiff_snd))
  let cs₁ : ChartedSpace (MorseModel m) ↥({x | f x = 1} : Set M) :=
    manifoldLevelSetChartedSpace J f 1 hfJ hregc
  have hm₁ : IsManifold 𝓘(ℝ, MorseModel m) ∞ ↥({x | f x = 1} : Set M) :=
    manifoldLevelSetIsManifold J f 1 hfJ hregc
  have hincJ : ContMDiff 𝓘(ℝ, MorseModel m) J ∞
      (fun x : ↥({x | f x = 1} : Set M) => (x : M)) :=
    contMDiff_levelSetInclusion J f 1 hfJ hregc
  have hinc : ContMDiff 𝓘(ℝ, MorseModel m) I ∞
      (fun x : ↥({x | f x = 1} : Set M) => (x : M)) :=
    e.contMDiff_transContinuousLinearEquiv_right.mp hincJ
  have h1mem : (1 : ℝ) ∈ Icc a b := ⟨ha1, h1b⟩
  have hmemL : ∀ y, η y ∈ Icc a b → f (Φ (1 - η y) y) = 1 := by
    intro y hy
    have h1 := hval y hy 1 h1mem
    rw [hfη _ (by rw [h1]; exact h1mem), h1]
  -- the two coordinate maps
  let Fm : ↥({x | f x = 1} : Set M) × ℝ → M := fun z => Φ (z.2 - 1) z.1
  have hFm : ContMDiff ((𝓘(ℝ, MorseModel m)).prod 𝓘(ℝ, ℝ)) I ∞ Fm :=
    hΦc.comp ((contMDiff_snd.sub contMDiff_const).prodMk (hinc.comp contMDiff_fst))
  let Gm : M → ↥({x | f x = 1} : Set M) := fun y =>
    if hy : η y ∈ Icc a b then ⟨Φ (1 - η y) y, hmemL y hy⟩ else ⟨x₀, hx₀⟩
  have hGm_val : ∀ y, η y ∈ Icc a b → (Gm y : M) = Φ (1 - η y) y := by
    intro y hy
    simp only [Gm, hy, ↓reduceDIte]
  set Bset : Set M := {y | a < η y ∧ η y < b} with hBset
  have hBo : IsOpen Bset :=
    (isOpen_lt continuous_const hη).inter (isOpen_lt hη continuous_const)
  -- smoothness of the level component on the open band (factor property)
  let B : TopologicalSpace.Opens M := ⟨Bset, hBo⟩
  let Fb : B → M := fun y => Φ (1 - f y) y
  have hFb : ContMDiff J J ∞ Fb :=
    hΦJ.comp ((contMDiff_const.sub (hfJ.comp contMDiff_subtype_val)).prodMk
      contMDiff_subtype_val)
  have hBband : ∀ y : B, η (y : M) ∈ Icc a b := fun y => ⟨y.2.1.le, y.2.2.le⟩
  have hFa : ∀ y : B, f (Fb y) = 1 := by
    intro y
    change f (Φ (1 - f y) y) = 1
    rw [hfη _ (hBband y)]
    exact hmemL _ (hBband y)
  have hfac := contMDiff_levelSet_factor J f 1 hfJ hregc Fb hFb hFa
  have hGm : ∀ y ∈ Bset, ContMDiffAt I 𝓘(ℝ, MorseModel m) ∞ Gm y := by
    intro y hy
    have heq : (fun x : B => Gm x) = (fun x : B => (⟨Fb x, hFa x⟩ : LevelSetSpace f 1)) := by
      funext x
      apply Subtype.ext
      rw [hGm_val _ (hBband x)]
      change Φ (1 - η x) x = Φ (1 - f x) x
      rw [hfη _ (hBband x)]
    have h1 : ContMDiffAt J 𝓘(ℝ, MorseModel m) ∞ (fun x : B => Gm x) ⟨y, hy⟩ := by
      rw [heq]
      exact hfac ⟨y, hy⟩
    exact e.contMDiffAt_transContinuousLinearEquiv_left.mp (contMDiffAt_subtype_iff.mp h1)
  let prj : M → ↥({x | f x = 1} : Set M) × ℝ := fun y => (Gm y, η y)
  have hprj : ContMDiffOn I ((𝓘(ℝ, MorseModel m)).prod 𝓘(ℝ, ℝ)) ∞ prj Bset := fun y hy =>
    ((hGm y hy).prodMk (hηW.contMDiffAt (hW.mem_nhds (hbandW ⟨hy.1.le, hy.2.le⟩))))
      |>.contMDiffWithinAt
  have hηFm : ∀ z : ↥({x | f x = 1} : Set M) × ℝ, z.2 ∈ Icc a b → η (Fm z) = z.2 := by
    intro z hz
    have h1 := hval z.1 (by rw [hLη _ z.1.2]; exact h1mem) z.2 hz
    rw [hLη _ z.1.2] at h1
    exact h1
  let bc : PartialDiffeomorph I ((𝓘(ℝ, MorseModel m)).prod 𝓘(ℝ, ℝ)) M
      (↥({x | f x = 1} : Set M) × ℝ) ∞ :=
    { toFun := prj
      invFun := Fm
      source := Bset
      target := {z | a < z.2 ∧ z.2 < b}
      map_source' := fun y hy => hy
      map_target' := fun z hz => by
        change a < η (Fm z) ∧ η (Fm z) < b
        rw [hηFm z ⟨hz.1.le, hz.2.le⟩]
        exact hz
      left_inv' := fun y hy => by
        change Φ (η y - 1) (Gm y) = y
        rw [hGm_val y ⟨hy.1.le, hy.2.le⟩, ← hΦadd, show 1 - η y + (η y - 1) = 0 by ring, hΦ0]
      right_inv' := fun z hz => by
        have hz' : z.2 ∈ Icc a b := ⟨hz.1.le, hz.2.le⟩
        have h2 := hηFm z hz'
        refine Prod.ext (Subtype.ext ?_) h2
        change (Gm (Fm z) : M) = z.1
        rw [hGm_val _ (by rw [h2]; exact hz'), h2]
        change Φ (1 - z.2) (Φ (z.2 - 1) z.1) = z.1
        rw [← hΦadd, show z.2 - 1 + (1 - z.2) = 0 by ring, hΦ0]
      open_source := hBo
      open_target := (isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const)
      contMDiffOn_toFun := hprj
      contMDiffOn_invFun := hFm.contMDiffOn }
  exact ⟨cs₁, hm₁, bc, rfl, rfl, fun y hy => ⟨hGm_val y ⟨hy.1.le, hy.2.le⟩, rfl⟩,
    fun _ => rfl⟩

/-- **Open-band chart of a band flow.** `η` continuous, smooth on an open `W` containing its
compact band `η⁻¹[a, b]` (`a ≤ 1 ≤ b`), regular on the band, `Φ` a jointly smooth flow with
`η (Φ (s - η x) x) = s` on the band, and the level `η⁻¹(1)` nonempty. The level carries an
(embedded, regular-level) smooth structure for which `y ↦ (Φ (1 - η y) y, η y)` is a partial
diffeomorphism from the open band `{a < η < b}` onto `η⁻¹(1) × (a, b)`, with inverse
`(x, u) ↦ Φ (u - 1) x`. -/
theorem exists_openBand_levelChart [T2Space M] [SigmaCompactSpace M] {m : ℕ}
    (hdim : Module.finrank ℝ E = m + 1) {η : M → ℝ} (hη : Continuous η) {W : Set M}
    (hW : IsOpen W) (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {a b : ℝ} (hab : a < b)
    (ha1 : a ≤ 1) (h1b : 1 ≤ b) (hK : IsCompact (η ⁻¹' Icc a b)) (hKW : η ⁻¹' Icc a b ⊆ W)
    (hregη : ∀ x ∈ η ⁻¹' Icc a b, mfderiv I 𝓘(ℝ, ℝ) η x ≠ 0) {Φ : ℝ → M → M}
    (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2))
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hval : ∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s)
    (hne : ∃ x, η x = 1) :
    ∃ cs : ChartedSpace (MorseModel m) ↥({x | η x = 1} : Set M),
      letI := cs
      IsManifold 𝓘(ℝ, MorseModel m) ∞ ↥({x | η x = 1} : Set M) ∧
      ∃ bc : PartialDiffeomorph I (𝓘(ℝ, MorseModel m).prod 𝓘(ℝ, ℝ)) M
          (↥({x | η x = 1} : Set M) × ℝ) ∞,
        bc.source = {y | a < η y ∧ η y < b} ∧ bc.target = {z | a < z.2 ∧ z.2 < b} ∧
        (∀ y ∈ bc.source, ((bc y).1 : M) = Φ (1 - η y) y ∧ (bc y).2 = η y) ∧
        ∀ z, bc.symm z = Φ (z.2 - 1) z.1 := by
  obtain ⟨f, hf, ⟨O, hOo, hKO, -, hEq⟩, hlo, hhi⟩ :=
    exists_contMDiff_eqOn_band hη hW hηW hab hK hKW
  have hband : ∀ x, f x ∈ Icc a b ↔ η x ∈ Icc a b := fun x =>
    band_mem_Icc_iff hEq hKO hlo hhi
  have hfη : ∀ x, η x ∈ Icc a b → f x = η x := fun x hx => hEq (hKO hx)
  have hreg : ∀ x, f x ∈ Icc a b → ¬ IsCriticalPointAt I f x := by
    intro x hx hcrit
    have hx' : x ∈ η ⁻¹' Icc a b := (hband x).mp hx
    have hloc : f =ᶠ[𝓝 x] η := Filter.eventuallyEq_of_mem (hOo.mem_nhds (hKO hx')) hEq
    apply hregη x hx'
    change mfderiv I 𝓘(ℝ, ℝ) f x = 0 at hcrit
    rw [hloc.symm.mfderiv_eq, hcrit]
    exact ContinuousLinearMap.comp_zero _
  have hL : {x | f x = 1} = {x | η x = 1} :=
    Set.ext fun x => band_eq_iff hEq hKO hlo hhi ⟨ha1, h1b⟩
  obtain ⟨x₀, hx₀⟩ := hne
  exact openBandChart_aux hdim hf (fun x hx => hreg x (by rw [hx]; exact ⟨ha1, h1b⟩)) hη hW hηW
    ha1 h1b hKW hfη hΦc hΦadd hΦ0 hval hL (fun _ hx => hx) x₀ hx₀

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
private theorem mfderiv_ne_zero_of_mvfderiv_pos' {η : M → ℝ} {x : M}
    {v : TangentSpace I x} (h : 0 < mvfderiv (I := I) η x v) : mfderiv I 𝓘(ℝ, ℝ) η x ≠ 0 := by
  intro h0
  have hz : mvfderiv (I := I) η x v = 0 := by
    change NormedSpace.fromTangentSpace (η x) (mfderiv I 𝓘(ℝ, ℝ) η x v) = 0
    rw [h0]
    rfl
  linarith

end Chart

/-- **The interior of a band sublevel is the strict sublevel.** If a continuous flow moves a
continuous `η` with unit speed on its band `η⁻¹[a, b]`, then `int {η ≤ ρ} = {η < ρ}` for every
`ρ ∈ [a, b)`. -/
theorem interior_setOf_le_of_band_flow {X : Type*} [TopologicalSpace X] {η : X → ℝ}
    (hη : Continuous η) {Φ : ℝ → X → X} (hΦc : Continuous fun q : ℝ × X => Φ q.1 q.2)
    (hΦ0 : ∀ x, Φ 0 x = x) {a b ρ : ℝ} (hρ : ρ ∈ Ico a b)
    (hval : ∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s) :
    interior {x | η x ≤ ρ} = {x | η x < ρ} := by
  apply Subset.antisymm
  · intro y hy
    have hyle : η y ≤ ρ := (interior_subset hy : y ∈ {x | η x ≤ ρ})
    rcases lt_or_eq_of_le hyle with h | h
    · exact h
    · exfalso
      have hcont : Continuous fun s : ℝ => Φ s y :=
        hΦc.comp (continuous_id.prodMk continuous_const)
      have hnhds : (fun s : ℝ => Φ s y) ⁻¹' interior {x | η x ≤ ρ} ∈ 𝓝 (0 : ℝ) := by
        refine hcont.continuousAt.preimage_mem_nhds ?_
        rw [hΦ0]
        exact isOpen_interior.mem_nhds hy
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
      set s := min (δ / 2) (b - ρ) with hs
      have hs0 : 0 < s := lt_min (half_pos hδ) (by linarith [hρ.2])
      have hsb : s ≤ b - ρ := min_le_right _ _
      have hsδ : s ∈ Metric.ball (0 : ℝ) δ := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs0]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
      have hin : η (Φ s y) ≤ ρ := (interior_subset (hball hsδ) : Φ s y ∈ {x | η x ≤ ρ})
      have hyband : η y ∈ Icc a b := by rw [h]; exact ⟨hρ.1, hρ.2.le⟩
      have hval' := hval y hyband (ρ + s) ⟨by linarith [hρ.1], by linarith⟩
      rw [h, show ρ + s - ρ = s by ring] at hval'
      linarith
  · exact interior_maximal (fun x (hx : η x < ρ) => show η x ≤ ρ from le_of_lt hx)
      (isOpen_lt hη continuous_const)

section Riemannian

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [SigmaCompactSpace M] [CompleteSpace M] in
/-- **Short flow segments in a band.** If the flow lines of `Φ` have velocity `V` of speed at most
`C` while they stay in the band `η⁻¹[a, b]`, and `η` grows with unit speed along them, then
`d(Φ s y, y) ≤ C |s|` whenever `η y` and `η y + s` lie in `[a, b]`. -/
theorem dist_flow_le_of_speed_bound (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {Φ : ℝ → M → M}
    (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)) (hΦ0 : ∀ x, Φ 0 x = x)
    {η : M → ℝ} {a b C : ℝ} (hC : 0 ≤ C)
    (hval : ∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s)
    (V : (x : M) → TangentSpace I x)
    (hvel : ∀ x t, η (Φ t x) ∈ Icc a b →
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x))))
    (hspeed : ∀ y, η y ∈ Icc a b → √(g.inner y (V y) (V y)) ≤ C) :
    ∀ y, η y ∈ Icc a b → ∀ s, η y + s ∈ Icc a b → dist (Φ s y) y ≤ C * |s| := by
  intro y hy s hs
  have hsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun u => Φ u y) :=
    hΦc.comp (contMDiff_id.prodMk contMDiff_const)
  have hlev : ∀ u, η y + u ∈ Icc a b → η (Φ u y) = η y + u := by
    intro u hu
    have h1 := hval y hy (η y + u) hu
    rwa [add_sub_cancel_left] at h1
  have hspeed' : ∀ u, η y + u ∈ Icc a b →
      √(g.inner (Φ u y) (mfderiv 𝓘(ℝ, ℝ) I (fun s => Φ s y) u 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => Φ s y) u 1)) ≤ C := by
    intro u hu
    have hin : η (Φ u y) ∈ Icc a b := by rw [hlev u hu]; exact hu
    have hd := (hvel y u hin).mfderiv
    erw [hd]
    convert hspeed _ hin using 4 <;> exact one_smul ℝ _
  have hseg : ∀ s₁ s₂, s₁ ≤ s₂ → η y + s₁ ∈ Icc a b → η y + s₂ ∈ Icc a b →
      dist (Φ s₁ y) (Φ s₂ y) ≤ C * (s₂ - s₁) := by
    intro s₁ s₂ h12 h1 h2
    have hb := DifferentialGeometry.Geometry.riemannianEDistOf_le_of_curve_speed_bound g h12
      (hsm.contMDiffOn.of_le (by norm_num)) (C := C) (by
        intro u hu
        exact hspeed' u ⟨by linarith [h1.1, hu.1], by linarith [h2.2, hu.2]⟩)
    rw [← ENNReal.ofReal_mul hC, riemannianEDistOf_eq_riemannianEDist g hEnorm,
      ← IsRiemannianManifold.out (I := I), edist_dist] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sub_nonneg.mpr h12))).mp hb
  have hy0 : η y + 0 ∈ Icc a b := by rw [add_zero]; exact hy
  rcases le_total 0 s with h | h
  · have := hseg 0 s h hy0 hs
    rw [hΦ0, sub_zero, dist_comm] at this
    rwa [abs_of_nonneg h]
  · have := hseg s 0 h hs hy0
    rw [hΦ0, zero_sub] at this
    rwa [abs_of_nonpos h]

/-- **LC60: smooth open-distance-ball comparison with small displacement**
(`master207A.tex:23408`). In the LC32–LC34 setting (`ε < 1/4`, `e < 1/40`, `ρ ∈ [1/5, 2]`) there is
a partial diffeomorphism `J` of `M` (ambient smooth structure) from `int {η ≤ ρ}` onto the open
distance ball `B(p, ρ)`, the identity where `η ≤ ρ - 2e`, with displacement `< 3e / (1 - ε)`;
it fixes `p`. -/
theorem exists_open_distance_ball_diffeomorph {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M}
    {η : M → ℝ} {ε : ℝ≥0} {e : ℝ} (hε : (ε : ℝ) < 1 / 4) (he : e < 1 / 40)
    (hclose : ∀ x, |η x - dist p x| < e) (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤ g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
    ∃ J : PartialDiffeomorph I I M M ∞, J.source = interior {x | η x ≤ ρ} ∧
      J.target = Metric.ball p ρ ∧ (∀ x ∈ J.source, η x ≤ ρ - 2 * e → J x = x) ∧
      (∀ x ∈ J.source, dist (J x) x < 3 * e / (1 - ε)) ∧ p ∈ J.source ∧ J p = p := by
  have he0 : 0 < e := lt_of_le_of_lt (abs_nonneg _) (hclose p)
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hm : 0 < 1 - (ε : ℝ) := by linarith
  obtain ⟨Φ, hΦ0, hΦc, -, hΦadd, hval, -, hvel, hspeed, htrack, -⟩ :=
    radialBand_gradient_diffeomorph hdim g hEnorm (by linarith) he hclose hlip hW hCW hηW hgrad
  have hΦ0' : ∀ x, Φ 0 x = x := fun x => by rw [hΦ0]; rfl
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist p x))
  have : ProperSpace M :=
    ⟨fun x r => DifferentialGeometry.Geometry.Topology.soul_isCompact_closedBall
      (I := I) g hEnorm x r⟩
  have hK : IsCompact (η ⁻¹' Icc (1 / 8 : ℝ) 3) :=
    isCompact_preimage_of_abs_sub_dist_lt hη hclose isCompact_Icc
  have hKann := radialBand_subset_annulus hclose he
  have hKW : η ⁻¹' Icc (1 / 8 : ℝ) 3 ⊆ W := fun x hx =>
    hCW x (hKann hx).1.le (hKann hx).2.le
  have hregη : ∀ x ∈ η ⁻¹' Icc (1 / 8 : ℝ) 3, mfderiv I 𝓘(ℝ, ℝ) η x ≠ 0 := by
    intro x hx
    apply mfderiv_ne_zero_of_mvfderiv_pos' (v := gradientFun (I := I) g η x)
    rw [← inner_gradientFun (I := I) g η x]
    exact lt_of_lt_of_le (by positivity) (hgrad x (hKann hx).1.le (hKann hx).2.le)
  -- constants
  set c := ρ - 2 * e with hcdef
  have hac : (1 / 8 : ℝ) < c := by rw [hcdef]; linarith [hρ.1]
  have hcρ : c < ρ := by rw [hcdef]; linarith
  have hρb : ρ + e < 3 := by linarith [hρ.2]
  have hρa : 1 / 8 + e < ρ := by linarith [hρ.1]
  -- the crossing height of LC34 for the SAME flow
  have hR : ∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 → η (Φ (1 - η y) y) = 1 := fun y hy =>
    hval y hy 1 ⟨by norm_num, by norm_num⟩
  have hcomp : ∀ y u, Φ (u - 1) (Φ (1 - η y) y) = Φ (u - η y) y := by
    intro y u
    rw [← hΦadd, show 1 - η y + (u - 1) = u - η y by ring]
  have hcε : 0 < (1 - 2 * (ε : ℝ)) / (1 - ε) := div_pos (by linarith) hm
  have hslope : ∀ y, η y ∈ Icc (1 / 8 : ℝ) 3 → ∀ s t, 1 / 8 ≤ s → s ≤ t → t ≤ 3 →
      (1 - 2 * (ε : ℝ)) / (1 - ε) * (t - s) ≤
        dist p (Φ (t - η y) y) - dist p (Φ (s - η y) y) := by
    intro y hy s t hs hst ht
    have h := htrack (Φ (1 - η y) y) (hR y hy) s t hs hst ht
    rwa [hcomp, hcomp] at h
  obtain ⟨hρf, hρc, -, hρspec⟩ := exists_distance_crossing_height (X := M)
    (d := fun x => dist p x) hη (continuous_const.dist continuous_id) (Φ := fun t x => Φ t x)
    hΦc.continuous hΦadd hval hcε hslope hclose (ρ := ρ) hρa.le hρb.le
  have hdist := dist_flow_le_of_speed_bound g hEnorm (Φ := fun t x => Φ t x) hΦc hΦ0'
    (η := η) (a := 1 / 8) (b := 3) (C := (1 - (ε : ℝ))⁻¹) (inv_nonneg.mpr hm.le) hval
    (fun y => (g.inner y (gradientFun (I := I) g η y) (gradientFun (I := I) g η y))⁻¹ •
      gradientFun (I := I) g η y) hvel hspeed
  -- classification off the open band
  have hoff : ∀ y, ¬ (1 / 8 < η y ∧ η y < 3) → (η y < ρ ↔ dist p y < ρ) := by
    intro y hy
    have h := abs_lt.mp (hclose y)
    by_cases hlo : η y ≤ 1 / 8
    · exact ⟨fun _ => by linarith, fun _ => by linarith⟩
    · have hhi : 3 ≤ η y := by
        by_contra hcon
        exact hy ⟨lt_of_not_ge hlo, lt_of_not_ge hcon⟩
      exact ⟨fun h' => by linarith, fun h' => by linarith⟩
  have hU : IsOpen {x : M | η x < ρ} := isOpen_lt hη continuous_const
  have hint : interior {x | η x ≤ ρ} = {x | η x < ρ} :=
    interior_setOf_le_of_band_flow (Φ := fun t x => Φ t x) hη hΦc.continuous hΦ0'
      (a := 1 / 8) (b := 3)
      ⟨by linarith [hρ.1], by linarith [hρ.2]⟩ hval
  have hpη : η p < c := by
    have h := abs_lt.mp (hclose p)
    rw [dist_self, sub_zero] at h
    rw [hcdef]
    linarith [hρ.1]
  have hpos : 0 < 3 * e / (1 - ε) := by positivity
  by_cases hne : ∃ x, η x = 1
  swap
  · -- empty level: the open band is empty and the identity is the required map
    have hnoband : ∀ y, ¬ (1 / 8 < η y ∧ η y < 3) := fun y hy =>
      hne ⟨_, hR y ⟨hy.1.le, hy.2.le⟩⟩
    have hset : {x : M | η x < ρ} = Metric.ball p ρ := Set.ext fun y => by
      rw [Metric.mem_ball, dist_comm]
      exact hoff y (hnoband y)
    let J0 : PartialDiffeomorph I I M M ∞ :=
      { toFun := id
        invFun := id
        source := {x | η x < ρ}
        target := {x | η x < ρ}
        map_source' := fun _ h => h
        map_target' := fun _ h => h
        left_inv' := fun _ _ => rfl
        right_inv' := fun _ _ => rfl
        open_source := hU
        open_target := hU
        contMDiffOn_toFun := contMDiffOn_id
        contMDiffOn_invFun := contMDiffOn_id }
    refine ⟨J0, hint.symm, hset, fun _ _ _ => rfl, fun x _ => ?_, lt_trans hpη hcρ, rfl⟩
    change dist x x < _
    rw [dist_self]
    exact hpos
  obtain ⟨cs, hcsm, bc, hbcs, hbct, hbcval, hbcsymm⟩ :=
    exists_openBand_levelChart (Φ := fun t x => Φ t x) hdim hη hW hηW (a := 1 / 8) (b := 3)
      (by norm_num) (by norm_num)
      (by norm_num) hK hKW hregη hΦc hΦadd hΦ0' hval hne
  let _cs := cs
  have := hcsm
  have : CompactSpace ↥({x : M | η x = 1} : Set M) :=
    isCompact_iff_compactSpace.mp (hK.of_isClosed_subset (isClosed_eq hη continuous_const)
      (fun x (hx : η x = 1) => show η x ∈ Icc (1 / 8 : ℝ) 3 by rw [hx]; norm_num))
  have hLband : ∀ x : ↥({x : M | η x = 1} : Set M), η (x : M) ∈ Icc (1 / 8 : ℝ) 3 := by
    intro x
    have hx : η (x : M) = 1 := x.2
    rw [hx]
    norm_num
  let hL : ↥({x : M | η x = 1} : Set M) → ℝ := fun x => hρf x
  have hLc : Continuous hL := hρc.comp_continuous continuous_subtype_val hLband
  have hρL : ∀ x, |hL x - ρ| < e := fun x => (hρspec x (hLband x)).2.1
  have hcL : ∀ x, c < hL x := fun x => by
    have := abs_lt.mp (hρL x)
    rw [hcdef]
    linarith
  have hLb : ∀ x, hL x < 3 := fun x => by
    have := abs_lt.mp (hρL x)
    linarith
  have hcross : ∀ x : ↥({x : M | η x = 1} : Set M), ∀ u ∈ Icc (1 / 8 : ℝ) 3,
      (dist p (Φ (u - 1) x) < ρ ↔ u < hL x) := by
    intro x u hu
    have h := ((hρspec x (hLband x)).2.2.2 u hu).2.1
    have hx : η (x : M) = 1 := x.2
    rw [hx] at h
    exact h
  obtain ⟨P, hPs, hPt, hPfst, hPid, hPmono⟩ :=
    exists_openGraph_straightening (J := 𝓘(ℝ, MorseModel m)) (a := 1 / 8) (c := c) (r := ρ)
      hac hcρ hL hLc hcL
  -- chart facts
  have hbc_src : ∀ y, 1 / 8 < η y → η y < 3 → y ∈ bc.source := fun y h1 h2 => by
    rw [hbcs]
    exact ⟨h1, h2⟩
  have hbc2 : ∀ y ∈ bc.source, (bc y).2 = η y := fun y hy => (hbcval y hy).2
  have hbc_left : ∀ y ∈ bc.source, bc.symm (bc y) = y := fun y hy => bc.left_inv' hy
  have hbc_right : ∀ z ∈ bc.target, bc (bc.symm z) = z := fun z hz => bc.right_inv' hz
  have hηsymm : ∀ z ∈ bc.target, η (bc.symm z) = z.2 := by
    intro z hz
    have h2 := hbc2 _ (bc.map_target' hz)
    change (bc (bc.symm z)).2 = η (bc.symm z) at h2
    rw [hbc_right z hz] at h2
    exact h2.symm
  -- straightening facts
  have hP_src : ∀ z : ↥({x : M | η x = 1} : Set M) × ℝ, 1 / 8 < z.2 → z.2 < ρ → z ∈ P.source :=
    fun z h1 h2 => by
      rw [hPs]
      exact ⟨h1, h2⟩
  have hP_tgt : ∀ z ∈ P.source, 1 / 8 < (P z).2 ∧ (P z).2 < hL (P z).1 := fun z hz => by
    have h := P.map_source' hz
    change P z ∈ P.target at h
    rw [hPt] at h
    exact h
  have hP_gtc : ∀ z ∈ P.source, c < z.2 → c < (P z).2 := by
    intro z hz hcz
    have hzc : ((z.1, c) : ↥({x : M | η x = 1} : Set M) × ℝ) ∈ P.source := hP_src _ hac hcρ
    have hid := hPid _ hzc le_rfl
    have hzs : z.2 ∈ Ioo (1 / 8 : ℝ) ρ := by
      rw [hPs] at hz
      exact hz
    have hlt : (P (z.1, c)).2 < (P (z.1, z.2)).2 := hPmono z.1 ⟨hac, hcρ⟩ hzs hcz
    rw [hid] at hlt
    exact hlt
  have hband_data : ∀ y, 1 / 8 < η y → η y < ρ → y ∈ bc.source ∧ bc y ∈ P.source ∧
      P (bc y) ∈ bc.target ∧ (P (bc y)).1 = (bc y).1 ∧ 1 / 8 < (P (bc y)).2 ∧
      (P (bc y)).2 < hL (bc y).1 := by
    intro y h1 h2
    have hs := hbc_src y h1 (by linarith)
    have hPs' := hP_src (bc y) (by rw [hbc2 y hs]; exact h1) (by rw [hbc2 y hs]; exact h2)
    have ht := hP_tgt _ hPs'
    have hf := hPfst _ hPs'
    rw [hf] at ht
    refine ⟨hs, hPs', ?_, hf, ht.1, ht.2⟩
    rw [hbct]
    exact ⟨ht.1, (ht.2).trans (hLb _)⟩
  -- the glued map
  let Jf : M → M := fun y => if 1 / 8 < η y ∧ η y < ρ then bc.symm (P (bc y)) else y
  have hJf_band : ∀ y, 1 / 8 < η y → η y < ρ → Jf y = bc.symm (P (bc y)) :=
    fun y h1 h2 => ite_eq_left ⟨h1, h2⟩
  have hJf_id : ∀ y, η y ≤ c → Jf y = y := by
    intro y hy
    by_cases h : 1 / 8 < η y ∧ η y < ρ
    · rw [hJf_band y h.1 h.2]
      have hs := hbc_src y h.1 (by linarith)
      have hPs' := hP_src (bc y) (by rw [hbc2 y hs]; exact h.1) (by rw [hbc2 y hs]; exact h.2)
      rw [hPid _ hPs' (by rw [hbc2 y hs]; exact hy)]
      exact hbc_left y hs
    · exact ite_eq_right h
  -- local diffeomorphism
  let G := (bc.trans P).trans bc.symm
  have hG_src : ∀ y, 1 / 8 < η y → η y < ρ → y ∈ G.source := by
    intro y h1 h2
    obtain ⟨hs, hPs', ht, -⟩ := hband_data y h1 h2
    exact ⟨⟨hs, hPs'⟩, ht⟩
  have hloc : IsLocalDiffeomorphOn I I ∞ Jf {x | η x < ρ} := by
    rintro ⟨y, hy⟩
    have hy' : η y < ρ := hy
    by_cases h1 : 1 / 8 < η y
    · have hev : Jf =ᶠ[𝓝 y] G := by
        filter_upwards [((isOpen_lt continuous_const hη).inter
          (isOpen_lt hη continuous_const)).mem_nhds ⟨h1, hy'⟩] with z hz
        exact hJf_band z hz.1 hz.2
      exact IsLocalDiffeomorphAt.of_eventuallyEq hev ⟨G, hG_src y h1 hy', fun _ _ => rfl⟩
    · have hyc : η y < c := by linarith
      have hev : Jf =ᶠ[𝓝 y] id := by
        filter_upwards [(isOpen_lt hη continuous_const).mem_nhds hyc] with z hz
        exact hJf_id z (le_of_lt hz)
      exact IsLocalDiffeomorphAt.of_eventuallyEq hev
        ⟨(Diffeomorph.refl I M ∞).toPartialDiffeomorph, mem_univ y, fun _ _ => rfl⟩
  -- injectivity
  have hlevJ : ∀ y, c < η y → η y < ρ → c < η (Jf y) := by
    intro y hc hρ'
    have h1 : 1 / 8 < η y := lt_trans hac hc
    obtain ⟨hs, hPs', ht, -, -, -⟩ := hband_data y h1 hρ'
    rw [hJf_band y h1 hρ', hηsymm _ ht]
    exact hP_gtc _ hPs' (by rw [hbc2 y hs]; exact hc)
  have hinj : InjOn Jf {x | η x < ρ} := by
    intro y₁ hy₁ y₂ hy₂ heq
    have hy₁' : η y₁ < ρ := hy₁
    have hy₂' : η y₂ < ρ := hy₂
    rcases le_or_gt (η y₁) c with h₁ | h₁ <;> rcases le_or_gt (η y₂) c with h₂ | h₂
    · rwa [hJf_id y₁ h₁, hJf_id y₂ h₂] at heq
    · exfalso
      have h3 := hlevJ y₂ h₂ hy₂'
      rw [← heq, hJf_id y₁ h₁] at h3
      linarith
    · exfalso
      have h3 := hlevJ y₁ h₁ hy₁'
      rw [heq, hJf_id y₂ h₂] at h3
      linarith
    · have hb₁ := hband_data y₁ (lt_trans hac h₁) hy₁'
      have hb₂ := hband_data y₂ (lt_trans hac h₂) hy₂'
      rw [hJf_band y₁ (lt_trans hac h₁) hy₁', hJf_band y₂ (lt_trans hac h₂) hy₂'] at heq
      have e1 : P (bc y₁) = P (bc y₂) := by
        have h3 : bc (bc.symm (P (bc y₁))) = bc (bc.symm (P (bc y₂))) := by rw [heq]
        rwa [hbc_right _ hb₁.2.2.1, hbc_right _ hb₂.2.2.1] at h3
      have e2 : bc y₁ = bc y₂ := P.toPartialEquiv.injOn hb₁.2.1 hb₂.2.1 e1
      exact bc.toPartialEquiv.injOn hb₁.1 hb₂.1 e2
  -- image
  have himg : Jf '' {x | η x < ρ} = Metric.ball p ρ := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : η y < ρ := hy
      rw [Metric.mem_ball, dist_comm]
      rcases le_or_gt (η y) c with h | h
      · rw [hJf_id y h]
        have := abs_lt.mp (hclose y)
        linarith
      · have h1 : 1 / 8 < η y := lt_trans hac h
        obtain ⟨-, -, -, hf, hlo, hhi⟩ := hband_data y h1 hy'
        rw [hJf_band y h1 hy', hbcsymm, hf]
        exact (hcross _ _ ⟨hlo.le, (hhi.trans (hLb _)).le⟩).mpr hhi
    · intro hw
      rw [Metric.mem_ball, dist_comm] at hw
      have hw' := abs_lt.mp (hclose w)
      rcases le_or_gt (η w) c with h | h
      · exact ⟨w, show η w < ρ by linarith, hJf_id w h⟩
      · have h1 : 1 / 8 < η w := lt_trans hac h
        have h3 : η w < 3 := by linarith
        have hs := hbc_src w h1 h3
        have hz2 : (bc w).2 = η w := hbc2 w hs
        have hwz : bc.symm (bc w) = w := hbc_left w hs
        have hzlt : (bc w).2 < hL (bc w).1 := by
          refine (hcross (bc w).1 (bc w).2 ⟨by rw [hz2]; exact h1.le,
            by rw [hz2]; exact h3.le⟩).mp ?_
          rw [← hbcsymm (bc w), hwz]
          exact hw
        have hzt : bc w ∈ P.target := by
          rw [hPt]
          exact ⟨by rw [hz2]; exact h1, hzlt⟩
        have hz₀s : P.symm (bc w) ∈ P.source := P.map_target' hzt
        have hPz₀ : P (P.symm (bc w)) = bc w := P.right_inv' hzt
        have hz₀2 : 1 / 8 < (P.symm (bc w)).2 ∧ (P.symm (bc w)).2 < ρ := by
          have h4 := hz₀s
          rw [hPs] at h4
          exact h4
        have hz₀t : P.symm (bc w) ∈ bc.target := by
          rw [hbct]
          exact ⟨hz₀2.1, by linarith [hz₀2.2]⟩
        have hη0 : η (bc.symm (P.symm (bc w))) = (P.symm (bc w)).2 := hηsymm _ hz₀t
        refine ⟨bc.symm (P.symm (bc w)), ?_, ?_⟩
        · change η (bc.symm (P.symm (bc w))) < ρ
          rw [hη0]
          exact hz₀2.2
        · rw [hJf_band _ (by rw [hη0]; exact hz₀2.1) (by rw [hη0]; exact hz₀2.2),
            hbc_right _ hz₀t, hPz₀, hwz]
  -- displacement
  have hdisp : ∀ y, η y < ρ → dist (Jf y) y < 3 * e / (1 - ε) := by
    intro y hy
    rcases le_or_gt (η y) c with h | h
    · rw [hJf_id y h, dist_self]
      exact hpos
    · have h1 : 1 / 8 < η y := lt_trans hac h
      obtain ⟨hs, hPs', -, hf, -, hhi⟩ := hband_data y h1 hy
      have hyrep : y = Φ (η y - 1) (bc y).1 := by
        have h2 := hbc_left y hs
        rw [hbcsymm, hbc2 y hs] at h2
        exact h2.symm
      have hJrep : Jf y = Φ ((P (bc y)).2 - η y) y := by
        rw [hJf_band y h1 hy, hbcsymm, hf]
        generalize (P (bc y)).2 = v
        have h2 : Φ (η y - 1 + (v - η y)) (bc y).1 = Φ (v - η y) y := by
          rw [hΦadd, ← hyrep]
        rw [← h2, show η y - 1 + (v - η y) = v - 1 by ring]
      have hcv : c < (P (bc y)).2 := hP_gtc _ hPs' (by rw [hbc2 y hs]; exact h)
      have hvu : |(P (bc y)).2 - η y| < 3 * e := by
        have := abs_lt.mp (hρL (bc y).1)
        rw [abs_lt]
        constructor <;> linarith
      have hvb : (P (bc y)).2 ≤ 3 := (hhi.trans (hLb _)).le
      have hd := hdist y ⟨h1.le, by linarith⟩ ((P (bc y)).2 - η y) ⟨by linarith, by linarith⟩
      rw [hJrep]
      calc dist (Φ ((P (bc y)).2 - η y) y) y ≤ (1 - (ε : ℝ))⁻¹ * |(P (bc y)).2 - η y| := hd
        _ < (1 - (ε : ℝ))⁻¹ * (3 * e) := mul_lt_mul_of_pos_left hvu (inv_pos.mpr hm)
        _ = 3 * e / (1 - ε) := by field_simp
  -- the partial diffeomorphism
  have hne' : ({x : M | η x < ρ}).Nonempty := ⟨p, lt_trans hpη hcρ⟩
  obtain ⟨Jpd, hJs, hJt, hJfun⟩ :=
    IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hloc hU hne' hinj
  have hJapp : ∀ y, Jpd y = Jf y := fun y => by rw [hJfun]
  refine ⟨Jpd, by rw [hJs, hint], by rw [hJt, himg], fun x _ hxc => ?_, fun x hx => ?_, ?_, ?_⟩
  · rw [hJapp]
    exact hJf_id x hxc
  · rw [hJapp]
    rw [hJs] at hx
    exact hdisp x hx
  · rw [hJs]
    exact lt_trans hpη hcρ
  · rw [hJapp]
    exact hJf_id p hpη.le

/-- LC60 in the blueprint's verbatim form (with the redundant hypothesis `0 < e`). -/
example {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M}
    {η : M → ℝ} {ε : ℝ≥0} {e : ℝ} (hε : (ε : ℝ) < 1 / 4) (he0 : 0 < e) (he : e < 1 / 40)
    (hclose : ∀ x, |η x - dist p x| < e) (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤ g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
    ∃ J : PartialDiffeomorph I I M M ∞, J.source = interior {x | η x ≤ ρ} ∧
      J.target = Metric.ball p ρ ∧ (∀ x ∈ J.source, η x ≤ ρ - 2 * e → J x = x) ∧
      ∀ x ∈ J.source, dist (J x) x < 3 * e / (1 - ε) := by
  obtain ⟨J, h1, h2, h3, h4, -⟩ := (fun _ => exists_open_distance_ball_diffeomorph hdim g hEnorm
    hε he hclose hlip hW hCW hηW hgrad hρ) he0
  exact ⟨J, h1, h2, h3, h4⟩

end Riemannian

end DifferentialGeometry.Geometry.Collapse
