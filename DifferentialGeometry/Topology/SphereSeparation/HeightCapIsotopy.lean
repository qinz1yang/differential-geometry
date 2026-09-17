import DifferentialGeometry.Topology.SphereSeparation.HeightCapVelocity
import DifferentialGeometry.Topology.SphereSeparation.HeightLevel
import DifferentialGeometry.Topology.Embedding.RelativeAmbientIsotopy
import DifferentialGeometry.Topology.Embedding.Factor
import DifferentialGeometry.Topology.Embedding.LinearEquiv

open Set Metric Filter Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem exists_ambient_isotopy_eqOn_quadratic_cap_models
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} {a b c₀ c₁ δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hδab : 4 * δ < b - a) (hc₀ : c₀ < a - δ) (hc₁ : b + δ < c₁)
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e (Icc a b ×ˢ univ))
    (hemb : ∀ t ∈ Icc a b, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    (A₀ A₁ : (V × ℝ) ≃ₘ[ℝ] (V × ℝ))
    (hA₀ : ∀ z, (A₀ z).2 = z.2) (hA₁ : ∀ z, (A₁ z).2 = z.2)
    (hv₀ : ∀ t ∈ Ioo (a - δ) (a + δ), ∀ x,
      HasDerivWithinAt (fun s => e (s, x))
        (A₀.quadraticFiberVectorField c₀ (t, e (t, x))) (Icc a b) t)
    (hv₁ : ∀ t ∈ Ioo (b - δ) (b + δ), ∀ x,
      HasDerivWithinAt (fun s => e (s, x))
        (A₁.quadraticFiberVectorField c₁ (t, e (t, x))) (Icc a b) t)
    {K : Set V} (hK : IsCompact K) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun z : ℝ × V => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × V => (Φ z.1).symm z.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x)) ∧
      (∀ t ∈ Icc (a - δ / 2) (a + δ / 2), ∀ x ∈ K,
        Φ t ((Φ a).symm (A₀ (x, a)).1) = (A₀ (quadraticLevelScaling a c₀ x t, t)).1) ∧
      (∀ t ∈ Icc (b - δ / 2) (b + δ / 2), ∀ x ∈ K,
        Φ t ((Φ b).symm (A₁ (x, b)).1) = (A₁ (quadraticLevelScaling b c₁ x t, t)).1) ∧
      ∃ S : Set V, IsCompact S ∧ ∀ t : ℝ, EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  let U₀ : Set (ℝ × V) := Ioo (a - δ) (a + δ) ×ˢ univ
  let U₁ : Set (ℝ × V) := Ioo (b - δ) (b + δ) ×ˢ univ
  let U := U₀ ∪ U₁
  let m := (a + b) / 2
  let W : ℝ × V → V := fun z => if z.1 < m then
    A₀.quadraticFiberVectorField c₀ z else A₁.quadraticFiberVectorField c₁ z
  have hmid₀ {t : ℝ} (ht : t ∈ Ioo (a - δ) (a + δ)) : t < m := by
    dsimp [m]
    linarith [ht.2]
  have hmid₁ {t : ℝ} (ht : t ∈ Ioo (b - δ) (b + δ)) : m < t := by
    dsimp [m]
    linarith [ht.1]
  have hU : IsOpen U := (isOpen_Ioo.prod isOpen_univ).union (isOpen_Ioo.prod isOpen_univ)
  have hW : ContDiffOn ℝ ∞ W U := by
    intro z hz
    rcases hz with hz | hz
    · have hzc : z.1 ≠ c₀ := by linarith [hz.1.1]
      have hmodel := (A₀.contDiffOn_quadraticFiberVectorField c₀ z hzc).contDiffAt
        ((isOpen_ne_fun continuous_fst continuous_const).mem_nhds hzc)
      apply (hmodel.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds (hmid₀ hz.1)] with y hy
      exact if_pos hy
    · have hzc : z.1 ≠ c₁ := by linarith [hz.1.2]
      have hmodel := (A₁.contDiffOn_quadraticFiberVectorField c₁ z hzc).contDiffAt
        ((isOpen_ne_fun continuous_fst continuous_const).mem_nhds hzc)
      apply (hmodel.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds (hmid₁ hz.1)] with y hy
      exact if_neg (not_lt.mpr hy.le)
  let γ₀ : V → ℝ → V := fun x t => (A₀ (quadraticLevelScaling a c₀ x t, t)).1
  let γ₁ : V → ℝ → V := fun x t => (A₁ (quadraticLevelScaling b c₁ x t, t)).1
  let C₀ : Set (ℝ × V) := (fun z : ℝ × V => (z.1, γ₀ z.2 z.1)) ''
    (Icc (a - δ / 2) (a + δ / 2) ×ˢ K)
  let C₁ : Set (ℝ × V) := (fun z : ℝ × V => (z.1, γ₁ z.2 z.1)) ''
    (Icc (b - δ / 2) (b + δ / 2) ×ˢ K)
  have hC₀ : IsCompact C₀ := (isCompact_Icc.prod hK).image
    (continuous_fst.prodMk (A₀.continuous_fst_comp_quadraticLevelScaling a c₀))
  have hC₁ : IsCompact C₁ := (isCompact_Icc.prod hK).image
    (continuous_fst.prodMk (A₁.continuous_fst_comp_quadraticLevelScaling b c₁))
  have htime₀ {t : ℝ} (ht : t ∈ Icc (a - δ / 2) (a + δ / 2)) :
      t ∈ Ioo (a - δ) (a + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htime₁ {t : ℝ} (ht : t ∈ Icc (b - δ / 2) (b + δ / 2)) :
      t ∈ Ioo (b - δ) (b + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hCsub : C₀ ∪ C₁ ⊆ U ∩ (univ ×ˢ univ) := by
    rintro z (hz | hz)
    · obtain ⟨⟨t, x⟩, ⟨ht, _⟩, rfl⟩ := hz
      exact ⟨Or.inl ⟨htime₀ ht, mem_univ _⟩, mem_univ _, mem_univ _⟩
    · obtain ⟨⟨t, x⟩, ⟨ht, _⟩, rfl⟩ := hz
      exact ⟨Or.inr ⟨htime₁ ht, mem_univ _⟩, mem_univ _, mem_univ _⟩
  have hWe (t : ℝ) (_ : t ∈ Icc a b) (x : M) (hx : (t, e (t, x)) ∈ U) :
      HasDerivWithinAt (fun s => e (s, x)) (W (t, e (t, x))) (Icc a b) t := by
    rcases hx with hx | hx
    · simpa only [W, if_pos (hmid₀ hx.1)] using hv₀ t hx.1 x
    · simpa only [W, if_neg (not_lt.mpr (hmid₁ hx.1).le)] using hv₁ t hx.1 x
  let γ : K ⊕ K → ℝ → V := Sum.elim (fun x => γ₀ x.val) (fun x => γ₁ x.val)
  let l : K ⊕ K → ℝ := Sum.elim (fun _ => a - δ / 2) (fun _ => b - δ / 2)
  let u : K ⊕ K → ℝ := Sum.elim (fun _ => a + δ / 2) (fun _ => b + δ / 2)
  have hγ (x : K ⊕ K) : ContinuousOn (γ x) (Icc (l x) (u x)) := by
    cases x with
    | inl x => exact ((A₀.continuous_fst_comp_quadraticLevelScaling a c₀).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    | inr x => exact ((A₁.continuous_fst_comp_quadraticLevelScaling b c₁).comp
        (continuous_id.prodMk continuous_const)).continuousOn
  have hγ' (x : K ⊕ K) (t : ℝ) (ht : t ∈ Ico (l x) (u x)) :
      HasDerivWithinAt (γ x) (W (t, γ x t)) (Ici t) t := by
    cases x with
    | inl x =>
      have ht' := htime₀ ⟨ht.1, ht.2.le⟩
      have hpos : 0 < (t - c₀) / (a - c₀) := div_pos (by linarith [ht'.1]) (by linarith)
      simp only [W, if_pos (hmid₀ ht')]
      convert! (A₀.hasDerivAt_fst_comp_quadraticLevelScaling
        hA₀ a c₀ x.val hpos).hasDerivWithinAt (s := Ici t) using 1
    | inr x =>
      have ht' := htime₁ ⟨ht.1, ht.2.le⟩
      have hpos : 0 < (t - c₁) / (b - c₁) :=
        div_pos_of_neg_of_neg (by linarith [ht'.2]) (by linarith)
      simp only [W, if_neg (not_lt.mpr (hmid₁ ht').le)]
      convert! (A₁.hasDerivAt_fst_comp_quadraticLevelScaling
        hA₁ b c₁ x.val hpos).hasDerivWithinAt (s := Ici t) using 1
  have hγC (x : K ⊕ K) (t : ℝ) (ht : t ∈ Icc (l x) (u x)) : (t, γ x t) ∈ C₀ ∪ C₁ := by
    cases x with
    | inl x => exact Or.inl ⟨(t, x.val), ⟨ht, x.property⟩, rfl⟩
    | inr x => exact Or.inr ⟨(t, x.val), ⟨ht, x.property⟩, rfl⟩
  obtain ⟨Φ, hΦ, hΦinv, hΦa, hΦe, hΦγ, S, hS, _, hfix⟩ :=
    exists_contDiff_compact_ambient_isotopy_Icc_eqOn_integralCurve hab he hemb
      isOpen_univ (subset_univ _) hU (hC₀.union hC₁) hCsub hW hWe hγ hγ' hγC
  have htrack (x : K ⊕ K) (v : ℝ) (hv : v ∈ Icc (l x) (u x))
      (t : ℝ) (ht : t ∈ Icc (l x) (u x)) :
      Φ t ((Φ v).symm (γ x v)) = γ x t := by
    have hbase : (Φ v).symm (γ x v) = (Φ (l x)).symm (γ x (l x)) := by
      rw [← hΦγ x v hv, (Φ v).symm_apply_apply]
    rw [hbase]
    exact hΦγ x t ht
  refine ⟨Φ, hΦ, hΦinv, hΦa, fun t ht x => (hΦe t ht x).1, ?_, ?_, S, hS, hfix⟩
  · intro t ht x hx
    have h := htrack (Sum.inl ⟨x, hx⟩) a ⟨by dsimp [l]; linarith, by dsimp [u]; linarith⟩ t ht
    have hac : a ≠ c₀ := by linarith
    simpa only [γ, Sum.elim_inl, γ₀, quadraticLevelScaling_self hac] using h
  · intro t ht x hx
    have h := htrack (Sum.inr ⟨x, hx⟩) b ⟨by dsimp [l]; linarith, by dsimp [u]; linarith⟩ t ht
    have hbc : b ≠ c₁ := by linarith
    simpa only [γ, Sum.elim_inr, γ₁, quadraticLevelScaling_self hbc] using h

theorem exists_height_level_isotopy_eqOn_extremum_neighborhoods
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {p q : SphereTwo}
    (hp : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p)
    (hq : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) q)
    (hmin : ∀ x, x ≠ p → e p 2 < e x 2)
    (hmax : ∀ x, x ≠ q → e x 2 < e q 2) (hpq : p ≠ q)
    (hcrit : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x → x = p ∨ x = q) :
    ∃ r : ℝ, 0 < r ∧ e p 2 + r ^ 2 / 2 < e q 2 - r ^ 2 / 2 ∧
      ∃ A₀ A₁ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ),
        (∀ z, (A₀ z).2 = z.2) ∧ (∀ z, (A₁ z).2 = z.2) ∧
        (EuclideanSpace.equivProdLast 2 ∘ e) '' {x | e x 2 ≤ e p 2 + r ^ 2 / 2} =
          (fun y => A₀ (y, e p 2 + 1 / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
        (EuclideanSpace.equivProdLast 2 ∘ e) '' {x | e q 2 - r ^ 2 / 2 ≤ e x 2} =
          (fun y => A₁ (y, e q 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
        ∃ Φ : ℝ → (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
          ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => Φ z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => (Φ z.1).symm z.2) ∧
          Φ (e p 2 + r ^ 2 / 2) = Diffeomorph.refl (𝓡 2) (EuclideanSpace ℝ (Fin 2)) ∞ ∧
          (∀ t ∈ Icc (e p 2 + r ^ 2 / 2) (e q 2 - r ^ 2 / 2),
            Φ t '' ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) ''
              {x | e x 2 = e p 2 + r ^ 2 / 2}) =
              (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t}) ∧
          (∃ S : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S ∧ ∀ t : ℝ,
            EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ) ∧
          ∃ η : ℝ, 0 < η ∧ η ≤ r ^ 2 / 8 ∧
            8 * η < (e q 2 - r ^ 2 / 2) - (e p 2 + r ^ 2 / 2) ∧
            ∃ R : ℝ, r < R ∧
            (∀ t ∈ Icc (e p 2 + r ^ 2 / 2 - η) (e p 2 + r ^ 2 / 2 + η),
              ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
                Φ t (A₀ (x, e p 2 + r ^ 2 / 2)).1 =
                  (A₀ (quadraticLevelScaling (e p 2 + r ^ 2 / 2) (e p 2) x t, t)).1) ∧
            (∀ t ∈ Icc (e q 2 - r ^ 2 / 2 - η) (e q 2 - r ^ 2 / 2 + η),
              ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
                Φ t ((Φ (e q 2 - r ^ 2 / 2)).symm (A₁ (x, e q 2 - r ^ 2 / 2)).1) =
                  (A₁ (quadraticLevelScaling (e q 2 - r ^ 2 / 2) (e q 2) x t, t)).1) := by
  obtain ⟨r, hr, hab, A₀, A₁, hA₀, hA₁, hcap₀, hcap₁,
      F, hF, _, hFa, hFlevels, δ, hδ, hδr, hδab, hv₀, hv₁⟩ :=
    exists_height_transport_with_quadratic_cap_velocity he hp hq hmin hmax hpq hcrit
  let a := e p 2 + r ^ 2 / 2
  let b := e q 2 - r ^ 2 / 2
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hra (x : SphereTwo) (hx : e x 2 = a) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0 := by
    intro hxcrit
    rcases hcrit x hxcrit with rfl | rfl <;> dsimp [a] at hx <;>
      nlinarith [sq_pos_of_pos hr]
  obtain ⟨C, S, hinc, _, _, _⟩ := exists_height_level_manifold he a hra
  let _ := C
  let _ := S
  let T := {x : SphereTwo // e x 2 = a}
  let : CompactSpace T := isCompact_iff_compactSpace.mp
    (isClosed_eq hf.continuous continuous_const).isCompact
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let G : ℝ × T → EuclideanSpace ℝ (Fin 2) × ℝ := fun z => L (e (F z.1 z.2.val))
  let J : ℝ × T → EuclideanSpace ℝ (Fin 2) := fun z => (G z).1
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, MorseModel 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ G :=
    L.contDiff.contMDiff.comp (he.contMDiff.comp (hF.comp (contMDiff_fst.prodMk
      (hinc.contMDiff.comp contMDiff_snd))))
  have hJ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, MorseModel 1)) (𝓡 2) ∞ J :=
    contDiff_fst.contMDiff.comp hG
  have hGemb (t : ℝ) : IsSmoothEmbedding 𝓘(ℝ, MorseModel 1)
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ (fun x => G (t, x)) := by
    have hD :=
      DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      (F t).isLocalDiffeomorph (F t).injective
    exact (he.comp (hD.comp hinc (by simp)) (by simp)).continuousLinearEquiv_comp L
  have hheight (t : ℝ) (ht : t ∈ Icc a b) (x : T) : (G (t, x)).2 = t :=
    (hFlevels t ht).subset ⟨x.val, x.property, rfl⟩
  have hJemb (t : ℝ) (ht : t ∈ Icc a b) :
      IsSmoothEmbedding 𝓘(ℝ, MorseModel 1) (𝓡 2) ∞ (fun x => J (t, x)) :=
    (hGemb t).fst_of_snd_eq_const (by simp) (hheight t ht)
  obtain ⟨Φ, hΦ, hΦinv, hΦa, hΦJ, hΦ₀, hΦ₁, hsupport⟩ :=
    exists_ambient_isotopy_eqOn_quadratic_cap_models hab hδ hδab
      (by dsimp [a]; nlinarith [sq_pos_of_pos hr])
      (by dsimp [b]; nlinarith [sq_pos_of_pos hr])
      hJ.contMDiffOn hJemb A₀ A₁ hA₀ hA₁
      (fun t ht x => (hv₀ t ht x.val x.property).hasDerivWithinAt)
      (fun t ht x => (hv₁ t ht x.val x.property).hasDerivWithinAt)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (2 * r))
  have hrange (t : ℝ) (ht : t ∈ Icc a b) :
      range (fun x : T => J (t, x)) =
        (fun x => (L (e x)).1) '' {x | e x 2 = t} := by
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨F t x.val, (hFlevels t ht).subset ⟨x.val, x.property, rfl⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := (hFlevels t ht).symm.subset hx
      exact ⟨⟨y, hy⟩, congrArg (fun z => (L (e z)).1) hyx⟩
  refine ⟨r, hr, hab, A₀, A₁, hA₀, hA₁, hcap₀, hcap₁,
    Φ, hΦ, hΦinv, hΦa, ?_, hsupport, δ / 2, half_pos hδ, by linarith,
    by linarith, 2 * r, by linarith, ?_, hΦ₁⟩
  · intro t ht
    change Φ t '' ((fun x => (L (e x)).1) '' {x | e x 2 = a}) = _
    rw [← hrange a ⟨le_rfl, hab.le⟩, ← range_comp]
    exact (congrArg range (funext (hΦJ t ht))).trans (hrange t ht)
  · intro t ht x hx
    simpa only [hΦa, Diffeomorph.symm_refl, Diffeomorph.coe_refl, id_eq] using hΦ₀ t ht x hx

theorem exists_height_level_isotopy_eqOn_extremum_disks
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {p q : SphereTwo}
    (hp : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p)
    (hq : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) q)
    (hmin : ∀ x, x ≠ p → e p 2 < e x 2)
    (hmax : ∀ x, x ≠ q → e x 2 < e q 2) (hpq : p ≠ q)
    (hcrit : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x → x = p ∨ x = q) :
    ∃ r : ℝ, 0 < r ∧ e p 2 + r ^ 2 / 2 < e q 2 - r ^ 2 / 2 ∧
      ∃ A₀ A₁ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ),
        (∀ z, (A₀ z).2 = z.2) ∧ (∀ z, (A₁ z).2 = z.2) ∧
        (EuclideanSpace.equivProdLast 2 ∘ e) '' {x | e x 2 ≤ e p 2 + r ^ 2 / 2} =
          (fun y => A₀ (y, e p 2 + 1 / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
        (EuclideanSpace.equivProdLast 2 ∘ e) '' {x | e q 2 - r ^ 2 / 2 ≤ e x 2} =
          (fun y => A₁ (y, e q 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r ∧
        ∃ Φ : ℝ → (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
          ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => Φ z.1 z.2) ∧
          ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => (Φ z.1).symm z.2) ∧
          Φ (e p 2 + r ^ 2 / 2) = Diffeomorph.refl (𝓡 2) (EuclideanSpace ℝ (Fin 2)) ∞ ∧
          (∀ t ∈ Icc (e p 2 + r ^ 2 / 2) (e q 2 - r ^ 2 / 2),
            Φ t '' ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) ''
              {x | e x 2 = e p 2 + r ^ 2 / 2}) =
              (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t}) ∧
          (∃ S : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S ∧ ∀ t : ℝ,
            EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ) ∧
          ∃ η : ℝ, 0 < η ∧ η ≤ r ^ 2 / 8 ∧
            8 * η < (e q 2 - r ^ 2 / 2) - (e p 2 + r ^ 2 / 2) ∧
            (∀ t ∈ Icc (e p 2 + r ^ 2 / 2 - η) (e p 2 + r ^ 2 / 2 + η),
              ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) r,
                Φ t (A₀ (x, e p 2 + r ^ 2 / 2)).1 =
                  (A₀ (quadraticLevelScaling (e p 2 + r ^ 2 / 2) (e p 2) x t, t)).1) ∧
            (∀ t ∈ Icc (e q 2 - r ^ 2 / 2 - η) (e q 2 - r ^ 2 / 2 + η),
              ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) r,
                Φ t ((Φ (e q 2 - r ^ 2 / 2)).symm (A₁ (x, e q 2 - r ^ 2 / 2)).1) =
                  (A₁ (quadraticLevelScaling (e q 2 - r ^ 2 / 2) (e q 2) x t, t)).1) := by
  obtain ⟨r, hr, hab, A₀, A₁, hA₀, hA₁, hcap₀, hcap₁,
    Φ, hΦ, hΦinv, hΦa, hlevels, hsupport, η, hη, hηr, hηab, R, hrR, h₀, h₁⟩ :=
      exists_height_level_isotopy_eqOn_extremum_neighborhoods he hp hq hmin hmax hpq hcrit
  exact ⟨r, hr, hab, A₀, A₁, hA₀, hA₁, hcap₀, hcap₁,
    Φ, hΦ, hΦinv, hΦa, hlevels, hsupport, η, hη, hηr, hηab,
    fun t ht x hx => h₀ t ht x (closedBall_subset_closedBall hrR.le hx),
    fun t ht x hx => h₁ t ht x (closedBall_subset_closedBall hrR.le hx)⟩

end DifferentialGeometry.Topology.SphereSeparation
