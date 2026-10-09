import DifferentialGeometry.Topology.Covering.PathLiftingCriterion
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Path.Composition
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PathLength

/-!
# Local isometries out of complete manifolds are coverings

* `exists_isPathLiftOn_of_isCompact`: along a local homeomorphism into a Hausdorff space, a
  path lifts from a point of the fibre over its start as soon as all partial lifts end in a
  fixed compact set.
* `isCoveringMap_of_isLocalIsometry`: a local isometry `f : N → M` from a complete
  Riemannian manifold `N` onto a connected Riemannian manifold `M` is a surjective covering
  map. Partial lifts of a smooth path are smooth and have the length of the path below them
  (`pathELength_comp_eq_of_enorm_mfderiv_eq`), so they stay in a closed metric ball of `N`,
  compact by Hopf–Rinow (`RiemannianMetricComplete.closedEBall_isCompact`). Smooth chart
  segments then show that the range of `f` is closed, and the covering criterion
  `isCoveringMap_of_forall_smooth_path_lift` concludes.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry

section Lift

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def IsPathLiftOn (F : X → Y) (γ : ℝ → Y) (z : X) (a t : ℝ) (η : ℝ → X) : Prop :=
  ContinuousOn η (Icc a t) ∧ η a = z ∧ ∀ s ∈ Icc a t, F (η s) = γ s

theorem IsPathLiftOn.extend {F : X → Y} {γ : ℝ → Y} {z : X} {a t u : ℝ} {η : ℝ → X}
    (hat : a ≤ t) (hγ : ContinuousOn γ (Icc t u)) (hη : IsPathLiftOn F γ z a t η)
    (e : OpenPartialHomeomorph X Y) (hFe : F = e) (hte : η t ∈ e.source)
    (htarget : MapsTo γ (Icc t u) e.target) :
    ∃ ζ : ℝ → X, IsPathLiftOn F γ z a u ζ := by
  classical
  let ζ : ℝ → X := (Iic t).piecewise η (e.symm ∘ γ)
  have hjoin : η t = e.symm (γ t) := by
    rw [← hη.2.2 t ⟨hat, le_rfl⟩, hFe, e.left_inv hte]
  refine ⟨ζ, ?_, ?_, ?_⟩
  · apply ContinuousOn.piecewise
    · intro s hs
      have hst : s = t := mem_singleton_iff.mp (frontier_Iic_subset t hs.2)
      rw [hst]
      exact hjoin
    · rw [closure_Iic]
      exact hη.1.mono fun s hs => ⟨hs.1.1, hs.2⟩
    · rw [compl_Iic, closure_Ioi]
      exact (e.continuousOn_symm.comp hγ htarget).mono fun s hs => ⟨hs.2, hs.1.2⟩
  · change (Iic t).piecewise η (e.symm ∘ γ) a = z
    rw [piecewise_eq_of_mem _ _ _ (show a ∈ Iic t from hat)]
    exact hη.2.1
  · intro s hs
    rcases le_or_gt s t with hst | hts
    · change F ((Iic t).piecewise η (e.symm ∘ γ) s) = γ s
      rw [piecewise_eq_of_mem _ _ _ (show s ∈ Iic t from hst)]
      exact hη.2.2 s ⟨hs.1, hst⟩
    · change F ((Iic t).piecewise η (e.symm ∘ γ) s) = γ s
      rw [piecewise_eq_of_notMem _ _ _ (show s ∉ Iic t from not_le.mpr hts), hFe]
      exact e.right_inv (htarget ⟨hts.le, hs.2⟩)

theorem exists_isPathLiftOn_of_isCompact [T2Space Y] {F : X → Y} (hF : IsLocalHomeomorph F)
    {γ : ℝ → Y} {z : X} {a b : ℝ} (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hz : F z = γ a) {K : Set X} (hK : IsCompact K)
    (hfence : ∀ t ∈ Icc a b, ∀ η : ℝ → X, IsPathLiftOn F γ z a t η → η t ∈ K) :
    ∃ η : ℝ → X, IsPathLiftOn F γ z a b η := by
  classical
  let S : Set ℝ := {t | t ∈ Icc a b ∧ ∃ η : ℝ → X, IsPathLiftOn F γ z a t η}
  have haS : a ∈ S := by
    refine ⟨⟨le_rfl, hab⟩, fun s => z, continuousOn_const, rfl, ?_⟩
    intro s hs
    rw [le_antisymm hs.2 hs.1]
    exact hz
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hSbdd : BddAbove S := ⟨b, fun t ht => ht.1.2⟩
  let t₀ : ℝ := sSup S
  have hat₀ : a ≤ t₀ := le_csSup hSbdd haS
  have ht₀b : t₀ ≤ b := csSup_le hSne fun t ht => ht.1.2
  have ht₀I : t₀ ∈ Icc a b := ⟨hat₀, ht₀b⟩
  have hnear : ∀ e : OpenPartialHomeomorph X Y, γ t₀ ∈ e.target →
      ∃ δ > 0, ∀ s ∈ Icc a b, |s - t₀| < δ → γ s ∈ e.target := by
    intro e he
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.mp
      ((hγ t₀ ht₀I).preimage_mem_nhdsWithin (e.open_target.mem_nhds he))
    refine ⟨δ, hδ, fun s hs hst => hδs ⟨?_, hs⟩⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact hst
  have ht₀S : t₀ ∈ S := by
    rcases hat₀.eq_or_lt with heq | hlt
    · rw [← heq]
      exact haS
    have hu : ∀ n : ℕ, ∃ u ∈ S, t₀ - 1 / ((n : ℝ) + 1) < u := fun n =>
      exists_lt_of_lt_csSup hSne (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith)
    choose u huS hut using hu
    choose η hη using fun n => (huS n).2
    let w : ℕ → X := fun n => η n (u n)
    have hwK : ∀ n, w n ∈ K := fun n => hfence (u n) (huS n).1 (η n) (hη n)
    obtain ⟨x, -, hx⟩ := hK (f := map w atTop) (le_principal_iff.mpr
      (mem_map.mpr (Eventually.of_forall hwK)))
    have hx' : MapClusterPt x atTop w := hx
    have hut₀ : Tendsto u atTop (𝓝[Icc a b] t₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => (huS n).1⟩
      refine tendsto_order.mpr ⟨fun c hc => ?_, fun c hc => ?_⟩
      · obtain ⟨n, hn⟩ := exists_nat_gt (1 / (t₀ - c))
        filter_upwards [eventually_ge_atTop n] with m hm
        have hpos : 0 < t₀ - c := by linarith
        have h1 : 1 / ((m : ℝ) + 1) < t₀ - c := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hpos] at hn
          have : (n : ℝ) ≤ m := by exact_mod_cast hm
          nlinarith
        linarith [hut m]
      · exact Eventually.of_forall fun n => lt_of_le_of_lt (le_csSup hSbdd (huS n)) hc
    have hγu : Tendsto (fun n => γ (u n)) atTop (𝓝 (γ t₀)) :=
      (hγ t₀ ht₀I).tendsto.comp hut₀
    have hFx : F x = γ t₀ := by
      by_contra hne
      obtain ⟨V, V', hV, hV', hxV, htV', hVV'⟩ := t2_separation hne
      have h1 : ∀ᶠ n in atTop, γ (u n) ∈ V' := hγu (hV'.mem_nhds htV')
      have h2 : ∃ᶠ n in atTop, w n ∈ F ⁻¹' V :=
        hx'.frequently ((hV.preimage hF.continuous).mem_nhds hxV)
      obtain ⟨n, hn1, hn2⟩ := (h2.and_eventually h1).exists
      have hwn : F (w n) = γ (u n) := (hη n).2.2 (u n) ⟨(huS n).1.1, le_rfl⟩
      exact Set.disjoint_left.mp hVV' hn1 (hwn ▸ hn2)
    obtain ⟨e, hxe, hFe⟩ := hF x
    have htarget : γ t₀ ∈ e.target := by
      rw [← hFx, hFe]
      exact e.map_source hxe
    obtain ⟨δ, hδ, hδs⟩ := hnear e htarget
    have h1 : ∀ᶠ n in atTop, t₀ - δ < u n :=
      (hut₀.mono_right nhdsWithin_le_nhds).eventually (lt_mem_nhds (by linarith))
    have h2 : ∃ᶠ n in atTop, w n ∈ e.source := hx'.frequently (e.open_source.mem_nhds hxe)
    obtain ⟨n, hn1, hn2⟩ := (h2.and_eventually h1).exists
    have hun : u n ≤ t₀ := le_csSup hSbdd (huS n)
    obtain ⟨ζ, hζ⟩ := (hη n).extend (huS n).1.1 (hγ.mono (Icc_subset_Icc (huS n).1.1 ht₀b))
      e hFe hn1 (fun s hs => hδs s ⟨(huS n).1.1.trans hs.1, hs.2.trans ht₀b⟩ (by
        rw [abs_lt]
        constructor <;> linarith [hs.1, hs.2]))
    exact ⟨ht₀I, ζ, hζ⟩
  have ht₀eq : t₀ = b := by
    by_contra hne
    have hlt : t₀ < b := lt_of_le_of_ne ht₀b hne
    obtain ⟨η₀, hη₀⟩ := ht₀S.2
    obtain ⟨e, hxe, hFe⟩ := hF (η₀ t₀)
    have htarget : γ t₀ ∈ e.target := by
      rw [← hη₀.2.2 t₀ ⟨hat₀, le_rfl⟩, hFe]
      exact e.map_source hxe
    obtain ⟨δ, hδ, hδs⟩ := hnear e htarget
    let u₁ : ℝ := min (t₀ + δ / 2) b
    have ht₀u₁ : t₀ < u₁ := lt_min (by linarith) hlt
    have hu₁b : u₁ ≤ b := min_le_right _ _
    obtain ⟨ζ, hζ⟩ := hη₀.extend hat₀ (hγ.mono (Icc_subset_Icc hat₀ hu₁b)) e hFe hxe
      (fun s hs => hδs s ⟨hat₀.trans hs.1, hs.2.trans hu₁b⟩ (by
        have : s ≤ t₀ + δ / 2 := hs.2.trans (min_le_left _ _)
        rw [abs_lt]
        constructor <;> linarith [hs.1]))
    exact (not_le.mpr ht₀u₁) (le_csSup hSbdd ⟨⟨hat₀.trans ht₀u₁.le, hu₁b⟩, ζ, hζ⟩)
  obtain ⟨η, hη⟩ := ht₀S.2
  rw [ht₀eq] at hη
  exact ⟨η, hη⟩

end Lift

section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {I : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold J ∞ N] [IsManifold I ∞ M] in
theorem IsPathLiftOn.contMDiffOn {f : N → M} (hf : IsLocalDiffeomorph J I ∞ f) {γ : ℝ → M}
    {z : N} {a t : ℝ} {η : ℝ → N} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a t))
    (hη : IsPathLiftOn f γ z a t η) : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ η (Icc a t) := by
  intro s hs
  obtain ⟨Φ, hsΦ, hfΦ⟩ := hf (η s)
  have htarget : γ s ∈ Φ.target := by
    rw [← hη.2.2 s hs, hfΦ hsΦ]
    exact Φ.map_source hsΦ
  have hsymm : ContMDiffAt I J ∞ Φ.symm (γ s) :=
    Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds htarget)
  have hev : ∀ᶠ r in 𝓝[Icc a t] s, η r ∈ Φ.source :=
    (hη.1 s hs).preimage_mem_nhdsWithin (Φ.open_source.mem_nhds hsΦ)
  have heq : η =ᶠ[𝓝[Icc a t] s] (Φ.symm ∘ γ) := by
    filter_upwards [hev, self_mem_nhdsWithin] with r hr hrI
    change η r = Φ.toPartialEquiv.symm (γ r)
    rw [← hη.2.2 r hrI, hfΦ hr]
    exact (Φ.toPartialEquiv.left_inv hr).symm
  exact (hsymm.comp_contMDiffWithinAt s (hγ s hs)).congr_of_eventuallyEq heq
    (heq.eq_of_nhdsWithin hs)

omit [FiniteDimensional ℝ E] [IsManifold J ∞ N] [IsManifold I ∞ M] in
theorem IsPathLiftOn.pathELength_eq [∀ x : N, ENorm (TangentSpace J x)]
    [∀ x : M, ENorm (TangentSpace I x)] {f : N → M} (hf : IsLocalDiffeomorph J I ∞ f)
    (hnorm : ∀ (x : N) (v : TangentSpace J x), ‖mfderiv J I f x v‖ₑ = ‖v‖ₑ) {γ : ℝ → M}
    {z : N} {a t : ℝ} {η : ℝ → N} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a t))
    (hη : IsPathLiftOn f γ z a t η) :
    Manifold.pathELength J η a t = Manifold.pathELength I γ a t := by
  have hηs := hη.contMDiffOn hf hγ
  have hdiff : ∀ᵐ s ∂MeasureTheory.volume.restrict (Ioo a t),
      MDifferentiableAt 𝓘(ℝ, ℝ) J η s :=
    (MeasureTheory.ae_restrict_mem measurableSet_Ioo).mono fun s hs =>
      ((hηs s (Ioo_subset_Icc_self hs)).mdifferentiableWithinAt (by simp)).mdifferentiableAt
        (Icc_mem_nhds hs.1 hs.2)
  rw [← Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq f hdiff
    (Eventually.of_forall fun s => (hf (η s)).mdifferentiableAt (by simp))
    (Eventually.of_forall fun s => hnorm _ _)]
  exact Manifold.pathELength_congr fun s hs => hη.2.2 s hs

variable [NeZero (Module.finrank ℝ E)] [J.Boundaryless] [T2Space N]
  [T2Space (TangentBundle J N)] [SigmaCompactSpace N] [I.Boundaryless] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] in
theorem forall_smooth_path_lift_of_isLocalIsometry (g : SmoothRiemannianMetric J N)
    (h : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g) {f : N → M}
    (hf : IsLocalDiffeomorph J I ∞ f)
    (hiso : ∀ (x : N) (v w : TangentSpace J x),
      h.inner (f x) (mfderiv J I f x v) (mfderiv J I f x w) = g.inner x v w)
    (γ : ℝ → M) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc 0 1)) (z : N) (hz : f z = γ 0) :
    ∃ η : ℝ → N, ContinuousOn η (Icc 0 1) ∧ η 0 = z ∧ ∀ t ∈ Icc (0 : ℝ) 1, f (η t) = γ t := by
  let rbN : RiemannianBundle (fun x : N => TangentSpace J x) := ⟨g.toRiemannianMetric⟩
  let rbM : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨h.toRiemannianMetric⟩
  have hgn : ∀ (x : N) (v : TangentSpace J x), ‖v‖ₑ = ENNReal.ofReal √(g.inner x v v) :=
    fun x v => Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hhn : ∀ (x : M) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal √(h.inner x v v) :=
    fun x v => Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm h x v
  have hnorm : ∀ (x : N) (v : TangentSpace J x), ‖mfderiv J I f x v‖ₑ = ‖v‖ₑ := by
    intro x v
    rw [hhn, hgn, hiso]
  have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) := hγ.of_le (by simp)
  have hfin : Manifold.pathELength I γ 0 1 ≠ ⊤ := by
    rw [Geometry.Riemannian.Geodesic.pathELength_eq_arcLength_of_enorm_eq (I := I) h
      zero_le_one ((Geometry.Riemannian.Geodesic.speedSqrt_integrableOn_Icc_of_C1 (I := I) h
        zero_le_one hγ1).mono_set Ioo_subset_Icc_self) (fun t ht => hhn (γ t) _)]
    exact ENNReal.ofReal_ne_top
  let L : ℝ := (Manifold.pathELength I γ 0 1).toReal
  obtain ⟨η, hη⟩ := exists_isPathLiftOn_of_isCompact hf.isLocalHomeomorph zero_le_one
    hγ.continuousOn hz (RiemannianMetricComplete.closedEBall_isCompact hg z L) (by
      intro t ht η hη
      have hγt : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc 0 t) := hγ.mono (Icc_subset_Icc le_rfl ht.2)
      have hηs := hη.contMDiffOn hf hγt
      change riemannianEDistOf g z (η t) ≤ ENNReal.ofReal L
      calc riemannianEDistOf g z (η t) = Manifold.riemannianEDist J z (η t) := rfl
        _ ≤ Manifold.pathELength J η 0 t :=
          Manifold.riemannianEDist_le_pathELength (hηs.of_le (by simp)) hη.2.1 rfl ht.1
        _ = Manifold.pathELength I γ 0 t := hη.pathELength_eq hf hnorm hγt
        _ ≤ Manifold.pathELength I γ 0 1 := Manifold.pathELength_mono le_rfl ht.2
        _ = ENNReal.ofReal L := (ENNReal.ofReal_toReal hfin).symm)
  exact ⟨η, hη.1, hη.2.1, hη.2.2⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem surjective_of_isLocalIsometry [ConnectedSpace M] [Nonempty N]
    (g : SmoothRiemannianMetric J N) (h : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete g) {f : N → M} (hf : IsLocalDiffeomorph J I ∞ f)
    (hiso : ∀ (x : N) (v w : TangentSpace J x),
      h.inner (f x) (mfderiv J I f x v) (mfderiv J I f x w) = g.inner x v w) :
    Surjective f := by
  have hclosed : IsClosed (range f) := by
    refine closure_subset_iff_isClosed.mp fun q hq => ?_
    let φ := extChartAt I q
    obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) q) (φ q)
      (mem_extChartAt_target q)
    let V : Set M := φ.source ∩ φ ⁻¹' Metric.ball (φ q) r
    have hVopen : IsOpen V := (continuousOn_extChartAt q).isOpen_inter_preimage
      (isOpen_extChartAt_source q) Metric.isOpen_ball
    have hqV : q ∈ V := ⟨mem_extChartAt_source q, Metric.mem_ball_self hr⟩
    obtain ⟨p, hpV, y, rfl⟩ := mem_closure_iff.mp hq V hVopen hqV
    let p : F := φ (f y)
    have hseg : ∀ s ∈ Icc (0 : ℝ) 1, p + s • (φ q - p) ∈ Metric.ball (φ q) r := fun s hs =>
      (convex_ball (φ q) r).add_smul_sub_mem hpV.2 (Metric.mem_ball_self hr) hs
    let γ : ℝ → M := fun s => φ.symm (p + s • (φ q - p))
    have hpath : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ (fun s : ℝ => p + s • (φ q - p)) :=
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff
    have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc 0 1) :=
      (contMDiffOn_extChartAt_symm q).comp hpath.contMDiffOn fun s hs => hrT (hseg s hs)
    have hγ0 : γ 0 = f y := by
      change φ.symm (p + (0 : ℝ) • (φ q - p)) = f y
      rw [zero_smul, add_zero]
      exact φ.left_inv hpV.1
    have hγ1 : γ 1 = q := by
      change φ.symm (p + (1 : ℝ) • (φ q - p)) = q
      rw [one_smul, add_sub_cancel]
      exact extChartAt_to_inv q
    obtain ⟨η, -, -, hη⟩ :=
      forall_smooth_path_lift_of_isLocalIsometry g h hg hf hiso γ hγ y hγ0.symm
    exact ⟨η 1, (hη 1 ⟨zero_le_one, le_rfl⟩).trans hγ1⟩
  have hclopen : IsClopen (range f) := ⟨hclosed, hf.isOpen_range⟩
  obtain ⟨y⟩ := (inferInstance : Nonempty N)
  exact range_eq_univ.mp (hclopen.eq_univ ⟨f y, mem_range_self y⟩)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isCoveringMap_of_isLocalIsometry [ConnectedSpace M] [Nonempty N]
    (g : SmoothRiemannianMetric J N) (h : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete g) {f : N → M} (hf : IsLocalDiffeomorph J I ∞ f)
    (hiso : ∀ (x : N) (v w : TangentSpace J x),
      h.inner (f x) (mfderiv J I f x v) (mfderiv J I f x w) = g.inner x v w) :
    IsCoveringMap f ∧ Surjective f := by
  have hsurj := surjective_of_isLocalIsometry g h hg hf hiso
  exact ⟨isCoveringMap_of_forall_smooth_path_lift hf.isLocalHomeomorph hsurj
    (forall_smooth_path_lift_of_isLocalIsometry g h hg hf hiso), hsurj⟩

end Riemannian

end DifferentialGeometry
