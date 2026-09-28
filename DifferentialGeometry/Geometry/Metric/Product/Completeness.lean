import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Completeness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry

open Bundle Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_fst_le_prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x y : M × N) :
    riemannianEDistOf (I := I) g x.1 y.1 ≤
      riemannianEDistOf (I := I.prod J) (g.prod h) x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine le_iInf fun γ => ?_
  refine le_iInf fun hγ => ?_
  let γ' : Path x.1 y.1 := γ.map continuous_fst
  have hγ' : CMDiff 1 γ' := by
    simpa only [γ', Path.map_coe, Function.comp_def] using
      (contMDiff_fst.comp hγ)
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (Real.sqrt
        (g.inner (γ' t) (mfderiv% γ' t 1) (mfderiv% γ' t 1))) :=
      iInf_le_of_le γ' (iInf_le_of_le hγ' le_rfl)
    _ ≤ ∫⁻ t, ENNReal.ofReal (Real.sqrt
        ((g.prod h).inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
      refine MeasureTheory.lintegral_mono fun t => ?_
      apply ENNReal.ofReal_le_ofReal
      apply Real.sqrt_le_sqrt
      have hder := mfderiv_comp_apply t
        (contMDiff_fst.contMDiffAt.mdifferentiableAt one_ne_zero)
        (hγ.contMDiffAt.mdifferentiableAt one_ne_zero) 1
      have hγ'fun : (γ' : unitInterval → M) = Prod.fst ∘ γ := by
        rfl
      rw [hγ'fun]
      change g.inner (γ t).1 (mfderiv% (Prod.fst ∘ γ) t 1)
          (mfderiv% (Prod.fst ∘ γ) t 1) ≤ _
      rw [hder, SmoothRiemannianMetric.prod_inner_mfderiv]
      apply le_add_of_nonneg_right
      let v := mfderiv (I.prod J) J Prod.snd (γ t) (mfderiv% γ t 1)
      by_cases hv : v = 0
      · change 0 ≤ h.inner (γ t).2 v v
        rw [hv]
        simp only [map_zero, le_refl]
      · exact (h.pos (γ t).2 v hv).le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_snd_le_prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x y : M × N) :
    riemannianEDistOf (I := J) h x.2 y.2 ≤
      riemannianEDistOf (I := I.prod J) (g.prod h) x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine le_iInf fun γ => ?_
  refine le_iInf fun hγ => ?_
  let γ' : Path x.2 y.2 := γ.map continuous_snd
  have hγ' : CMDiff 1 γ' := by
    simpa only [γ', Path.map_coe, Function.comp_def] using
      (contMDiff_snd.comp hγ)
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (Real.sqrt
        (h.inner (γ' t) (mfderiv% γ' t 1) (mfderiv% γ' t 1))) :=
      iInf_le_of_le γ' (iInf_le_of_le hγ' le_rfl)
    _ ≤ ∫⁻ t, ENNReal.ofReal (Real.sqrt
        ((g.prod h).inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
      refine MeasureTheory.lintegral_mono fun t => ?_
      apply ENNReal.ofReal_le_ofReal
      apply Real.sqrt_le_sqrt
      have hder := mfderiv_comp_apply t
        (contMDiff_snd.contMDiffAt.mdifferentiableAt one_ne_zero)
        (hγ.contMDiffAt.mdifferentiableAt one_ne_zero) 1
      have hγ'fun : (γ' : unitInterval → N) = Prod.snd ∘ γ := by
        rfl
      rw [hγ'fun]
      change h.inner (γ t).2 (mfderiv% (Prod.snd ∘ γ) t 1)
          (mfderiv% (Prod.snd ∘ γ) t 1) ≤ _
      rw [hder, SmoothRiemannianMetric.prod_inner_mfderiv]
      apply le_add_of_nonneg_left
      let v := mfderiv (I.prod J) I Prod.fst (γ t) (mfderiv% γ t 1)
      by_cases hv : v = 0
      · change 0 ≤ g.inner (γ t).1 v v
        rw [hv]
        simp only [map_zero, le_refl]
      · exact (g.pos (γ t).1 v hv).le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_prod_left
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x y : M) (z : N) :
    riemannianEDistOf (I := I.prod J) (g.prod h) (x, z) (y, z) =
      riemannianEDistOf (I := I) g x y := by
  apply le_antisymm
  · rw [edistOf_iInf, edistOf_iInf]
    refine le_iInf fun γ => ?_
    refine le_iInf fun hγ => ?_
    let γ' : Path (x, z) (y, z) := {
      toContinuousMap :=
        ⟨fun t => (γ t, z), γ.continuous.prodMk continuous_const⟩
      source' := by simp
      target' := by simp }
    have hγ' : CMDiff 1 γ' := by
      change ContMDiff (𝓡∂ 1) (I.prod J) 1 (fun t => (γ t, z))
      simpa using hγ.prodMk contMDiff_const
    calc
      _ ≤ ∫⁻ t, ENNReal.ofReal (Real.sqrt
          ((g.prod h).inner (γ' t) (mfderiv% γ' t 1) (mfderiv% γ' t 1))) :=
        iInf_le_of_le γ' (iInf_le_of_le hγ' le_rfl)
      _ = ∫⁻ t, ENNReal.ofReal (Real.sqrt
          (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
        apply MeasureTheory.lintegral_congr
        intro t
        have hpath : MDiffAt (fun s : unitInterval => (γ s, z)) t := by
          exact hγ'.contMDiffAt.mdifferentiableAt one_ne_zero
        have hfst := mfderiv_comp_apply t
          (contMDiff_fst.contMDiffAt.mdifferentiableAt one_ne_zero)
          hpath 1
        have hsnd := mfderiv_comp_apply t
          (contMDiff_snd.contMDiffAt.mdifferentiableAt one_ne_zero)
          hpath 1
        change ENNReal.ofReal (Real.sqrt
          ((g.prod h).inner (γ t, z)
            (mfderiv (𝓡∂ 1) (I.prod J) (fun s => (γ s, z)) t 1)
            (mfderiv (𝓡∂ 1) (I.prod J) (fun s => (γ s, z)) t 1))) = _
        rw [SmoothRiemannianMetric.prod_inner_mfderiv, ← hfst, ← hsnd]
        change ENNReal.ofReal (Real.sqrt
          (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1) +
            h.inner z (mfderiv% (fun _ : unitInterval => z) t 1)
              (mfderiv% (fun _ : unitInterval => z) t 1))) = _
        rw [mfderiv_const]
        simp
  · exact riemannianEDistOf_fst_le_prod g h (x, z) (y, z)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_prod_right
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M) (y z : N) :
    riemannianEDistOf (I := I.prod J) (g.prod h) (x, y) (x, z) =
      riemannianEDistOf (I := J) h y z := by
  apply le_antisymm
  · rw [edistOf_iInf, edistOf_iInf]
    refine le_iInf fun γ => ?_
    refine le_iInf fun hγ => ?_
    let γ' : Path (x, y) (x, z) := {
      toContinuousMap :=
        ⟨fun t => (x, γ t), continuous_const.prodMk γ.continuous⟩
      source' := by simp
      target' := by simp }
    have hγ' : CMDiff 1 γ' := by
      change ContMDiff (𝓡∂ 1) (I.prod J) 1 (fun t => (x, γ t))
      simpa using contMDiff_const.prodMk hγ
    calc
      _ ≤ ∫⁻ t, ENNReal.ofReal (Real.sqrt
          ((g.prod h).inner (γ' t) (mfderiv% γ' t 1) (mfderiv% γ' t 1))) :=
        iInf_le_of_le γ' (iInf_le_of_le hγ' le_rfl)
      _ = ∫⁻ t, ENNReal.ofReal (Real.sqrt
          (h.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
        apply MeasureTheory.lintegral_congr
        intro t
        have hpath : MDiffAt (fun s : unitInterval => (x, γ s)) t := by
          exact hγ'.contMDiffAt.mdifferentiableAt one_ne_zero
        have hfst := mfderiv_comp_apply t
          (contMDiff_fst.contMDiffAt.mdifferentiableAt one_ne_zero)
          hpath 1
        have hsnd := mfderiv_comp_apply t
          (contMDiff_snd.contMDiffAt.mdifferentiableAt one_ne_zero)
          hpath 1
        change ENNReal.ofReal (Real.sqrt
          ((g.prod h).inner (x, γ t)
            (mfderiv (𝓡∂ 1) (I.prod J) (fun s => (x, γ s)) t 1)
            (mfderiv (𝓡∂ 1) (I.prod J) (fun s => (x, γ s)) t 1))) = _
        rw [SmoothRiemannianMetric.prod_inner_mfderiv, ← hfst, ← hsnd]
        change ENNReal.ofReal (Real.sqrt
          (g.inner x (mfderiv% (fun _ : unitInterval => x) t 1)
              (mfderiv% (fun _ : unitInterval => x) t 1) +
            h.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) = _
        rw [mfderiv_const]
        simp
  · exact riemannianEDistOf_snd_le_prod g h (x, y) (x, z)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem RiemannianMetricComplete.prod
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    (hg : RiemannianMetricComplete (I := I) g)
    (hh : RiemannianMetricComplete (I := J) h) :
    RiemannianMetricComplete (I := I.prod J) (g.prod h) := by
  let : IsManifold (I.prod J) 1 (M × N) :=
    IsManifold.of_le (I := I.prod J) (M := M × N) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace (M × N) :=
    Manifold.metrizableSpace (I.prod J) (M × N)
  let : T3Space (M × N) := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle
      (fun x : M × N => TangentSpace (I.prod J) x) :=
    ⟨(g.prod h).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (E × F)
      (fun x : M × N => TangentSpace (I.prod J) x) :=
    ⟨(g.prod h).inner, (g.prod h).contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace (M × N) :=
    EMetricSpace.ofRiemannianMetric (I.prod J) (M × N)
  refine EMetric.complete_of_cauchySeq_tendsto (γ := M × N) fun s hs => ?_
  have hsProduct : ∀ ε > (0 : ENNReal), ∃ K,
      ∀ m, K ≤ m → ∀ n, K ≤ n →
        riemannianEDistOf (I := I.prod J) (g.prod h) (s m) (s n) < ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := EMetric.cauchySeq_iff.mp hs ε hε
    refine ⟨K, fun m hm n hn => ?_⟩
    change edist (s m) (s n) < ε
    exact hK m hm n hn
  change ∃ x, Filter.Tendsto s Filter.atTop (𝓝 x)
  have hsFst : ∃ x, Filter.Tendsto (fun n => (s n).1) Filter.atTop (𝓝 x) := by
    let : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    let : T3Space M := inferInstance
    let : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E
        (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    let : CompleteSpace M := hg.complete
    apply cauchySeq_tendsto_of_complete
    apply EMetric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨K, hK⟩ := hsProduct ε hε
    refine ⟨K, fun m hm n hn => ?_⟩
    change riemannianEDistOf (I := I) g (s m).1 (s n).1 < ε
    exact lt_of_le_of_lt
      (riemannianEDistOf_fst_le_prod g h (s m) (s n))
      (hK m hm n hn)
  have hsSnd : ∃ y, Filter.Tendsto (fun n => (s n).2) Filter.atTop (𝓝 y) := by
    let : IsManifold J 1 N :=
      IsManifold.of_le (I := J) (M := N) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    let : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
    let : T3Space N := inferInstance
    let : RiemannianBundle (fun x : N => TangentSpace J x) :=
      ⟨h.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle F
        (fun x : N => TangentSpace J x) :=
      ⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩
    let : EMetricSpace N := EMetricSpace.ofRiemannianMetric J N
    let : CompleteSpace N := hh.complete
    apply cauchySeq_tendsto_of_complete
    apply EMetric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨K, hK⟩ := hsProduct ε hε
    refine ⟨K, fun m hm n hn => ?_⟩
    change riemannianEDistOf (I := J) h (s m).2 (s n).2 < ε
    exact lt_of_le_of_lt
      (riemannianEDistOf_snd_le_prod g h (s m) (s n))
      (hK m hm n hn)
  obtain ⟨x, hx⟩ := hsFst
  obtain ⟨y, hy⟩ := hsSnd
  exact ⟨(x, y), by simpa only [Prod.eta] using hx.prodMk_nhds hy⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem RiemannianMetricComplete.fst_of_prod
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    (hgh : RiemannianMetricComplete (I := I.prod J) (g.prod h))
    (z : N) : RiemannianMetricComplete (I := I) g := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  refine EMetric.complete_of_cauchySeq_tendsto (γ := M) fun s hs => ?_
  let : IsManifold (I.prod J) 1 (M × N) :=
    IsManifold.of_le (I := I.prod J) (M := M × N) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace (M × N) :=
    Manifold.metrizableSpace (I.prod J) (M × N)
  let : T3Space (M × N) := inferInstance
  let : RiemannianBundle
      (fun x : M × N => TangentSpace (I.prod J) x) :=
    ⟨(g.prod h).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (E × F)
      (fun x : M × N => TangentSpace (I.prod J) x) :=
    ⟨(g.prod h).inner, (g.prod h).contMDiff.continuous,
      by intro x v w; rfl⟩
  let : EMetricSpace (M × N) :=
    EMetricSpace.ofRiemannianMetric (I.prod J) (M × N)
  let : CompleteSpace (M × N) := hgh.complete
  have hsProd : CauchySeq (fun n => (s n, z)) := by
    apply EMetric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨K, hK⟩ := EMetric.cauchySeq_iff.mp hs ε hε
    refine ⟨K, fun m hm n hn => ?_⟩
    change riemannianEDistOf (I := I.prod J) (g.prod h)
      (s m, z) (s n, z) < ε
    rw [riemannianEDistOf_prod_left]
    exact hK m hm n hn
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hsProd
  refine ⟨p.1, ?_⟩
  simpa only [Function.comp_def] using
    continuous_fst.continuousAt.tendsto.comp hp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem RiemannianMetricComplete.snd_of_prod
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    (hgh : RiemannianMetricComplete (I := I.prod J) (g.prod h))
    (x : M) : RiemannianMetricComplete (I := J) h := by
  let : IsManifold J 1 N :=
    IsManifold.of_le (I := J) (M := N) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
  let : T3Space N := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (fun y : N => TangentSpace J y) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F
      (fun y : N => TangentSpace J y) :=
    ⟨h.inner, h.contMDiff.continuous, by intro y v w; rfl⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric J N
  refine EMetric.complete_of_cauchySeq_tendsto (γ := N) fun s hs => ?_
  let : IsManifold (I.prod J) 1 (M × N) :=
    IsManifold.of_le (I := I.prod J) (M := M × N) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace (M × N) :=
    Manifold.metrizableSpace (I.prod J) (M × N)
  let : T3Space (M × N) := inferInstance
  let : RiemannianBundle
      (fun y : M × N => TangentSpace (I.prod J) y) :=
    ⟨(g.prod h).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (E × F)
      (fun y : M × N => TangentSpace (I.prod J) y) :=
    ⟨(g.prod h).inner, (g.prod h).contMDiff.continuous,
      by intro y v w; rfl⟩
  let : EMetricSpace (M × N) :=
    EMetricSpace.ofRiemannianMetric (I.prod J) (M × N)
  let : CompleteSpace (M × N) := hgh.complete
  have hsProd : CauchySeq (fun n => (x, s n)) := by
    apply EMetric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨K, hK⟩ := EMetric.cauchySeq_iff.mp hs ε hε
    refine ⟨K, fun m hm n hn => ?_⟩
    change riemannianEDistOf (I := I.prod J) (g.prod h)
      (x, s m) (x, s n) < ε
    rw [riemannianEDistOf_prod_right]
    exact hK m hm n hn
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hsProd
  refine ⟨p.2, ?_⟩
  simpa only [Function.comp_def] using
    continuous_snd.continuousAt.tendsto.comp hp

theorem RiemannianMetricComplete.prod_iff
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    [Nonempty M] [Nonempty N]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N} :
    RiemannianMetricComplete (I := I.prod J) (g.prod h) ↔
      RiemannianMetricComplete (I := I) g ∧
        RiemannianMetricComplete (I := J) h := by
  constructor
  · intro hgh
    exact ⟨hgh.fst_of_prod (Nonempty.some (inferInstance : Nonempty N)),
      hgh.snd_of_prod (Nonempty.some (inferInstance : Nonempty M))⟩
  · exact fun hgh => hgh.1.prod hgh.2

end DifferentialGeometry
