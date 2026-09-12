import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Continuation

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
namespace CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem X_congr {c d : CurveMap M} {t : ℝ} (h : ∀ z : ℝ, c.lift z t = d.lift z t) (x : ℝ) :
    c.X (I := I) x t = d.X (I := I) x t := by
  unfold CurveMap.X
  rw [funext h]
  rfl

omit [CompleteSpace E] in
theorem curvatureVector_congr {c d : CurveMap M} {g : ℝ → SmoothRiemannianMetric I M}
    {t : ℝ} (h : ∀ z : ℝ, c.lift z t = d.lift z t) (x : ℝ) :
    c.curvatureVector g x t = d.curvatureVector g x t := by
  have hX : ∀ y : ℝ, c.X (I := I) y t = d.X (I := I) y t := fun y => X_congr h y
  have hspeed : ∀ y : ℝ, c.speed g y t = d.speed g y t := by
    intro y
    unfold CurveMap.speed
    rw [h y, hX y]
  simp only [CurveMap.curvatureVector, CurveMap.Ds, CurveMap.unitTangent, CurveMap.Dx]
  rw [funext h]
  simp only [hX, hspeed]
  rfl

omit [CompleteSpace E] in
theorem IsSolutionOn.mono {g : ℝ → SmoothRiemannianMetric I M} {J K : Set ℝ}
    {c : CurveMap M}
    (hK : K ⊆ J) (huniq : ∀ t ∈ K, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) K t)
    (h : CurveMap.IsSolutionOn (I := I) c g J) :
    CurveMap.IsSolutionOn (I := I) c g K where
  smooth := h.smooth.mono (Set.prod_mono Subset.rfl hK)
  immersed := fun x t ht => h.immersed x t (hK ht)
  equation := by
    intro x t ht
    have hMD : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => c.lift x s) J t :=
      (c.time_slice_contMDiffWithinAt (I := I) J h.smooth x t (hK ht)).mdifferentiableWithinAt
        (by simp)
    have hmem : J ∈ 𝓝[K] t := Filter.mem_of_superset self_mem_nhdsWithin hK
    rw [CurveMap.velocity,
      hMD.mfderivWithin_mono_of_mem_nhdsWithin (huniq t ht) hmem, ← CurveMap.velocity]
    exact h.equation x t (hK ht)

omit [CompleteSpace E] in
theorem IsSolutionOn.mono_Icc {g : ℝ → SmoothRiemannianMetric I M} {a a' b' b : ℝ}
    (ha : a ≤ a') (hb : b' ≤ b) (hab : a' < b') {c : CurveMap M}
    (h : CurveMap.IsSolutionOn (I := I) c g (Icc a b)) :
    CurveMap.IsSolutionOn (I := I) c g (Icc a' b') :=
  h.mono (Icc_subset_Icc ha hb)
    (fun t ht => ((uniqueDiffOn_Icc hab) t ht).uniqueMDiffWithinAt)

omit [CompleteSpace E] in
theorem IsSolutionOn.glue {g : ℝ → SmoothRiemannianMetric I M} {a t₀ T u : ℝ}
    (hat₀ : a ≤ t₀) (ht₀T : t₀ < T) (hTu : T < u)
    {c₁ c₂ : CurveMap M}
    (h₁ : CurveMap.IsSolutionOn (I := I) c₁ g (Icc a T))
    (h₂ : CurveMap.IsSolutionOn (I := I) c₂ g (Icc t₀ u))
    (hagree : ∀ z t, t ∈ Icc t₀ T → c₁ z t = c₂ z t) :
    CurveMap.IsSolutionOn (I := I) (fun z t => if t ≤ T then c₁ z t else c₂ z t) g
      (Icc a u) := by
  set cJ : CurveMap M := fun z t => if t ≤ T then c₁ z t else c₂ z t with hcJ
  have heq₁ : ∀ z t, t ≤ T → cJ z t = c₁ z t := by
    intro z t ht
    simp only [hcJ, if_pos ht]
  have heq₂ : ∀ z t, t₀ < t → cJ z t = c₂ z t := by
    intro z t ht
    by_cases h : t ≤ T
    · simp only [hcJ, if_pos h, hagree z t ⟨le_of_lt ht, h⟩]
    · simp only [hcJ, if_neg h]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, t⟩ := p
    rcases lt_trichotomy t T with hlt | heq | hgt
    · have hV : (univ : Set ℝ) ×ˢ Iio T ∈ 𝓝 (x, t) :=
        (isOpen_univ.prod isOpen_Iio).mem_nhds
          (by simp only [Set.mem_prod, mem_univ, true_and, Set.mem_Iio]; exact hlt)
      have hsub : ((univ : Set ℝ) ×ˢ Iio T) ∩ (univ ×ˢ Icc a u) ⊆
          univ ×ˢ Icc a T := by
        rintro ⟨y, s⟩ ⟨⟨-, hs⟩, ⟨-, hsa, hsu⟩⟩
        exact ⟨mem_univ _, hsa, le_of_lt hs⟩
      have hmem : (univ ×ˢ Icc a T) ∈ 𝓝[univ ×ˢ Icc a u] (x, t) :=
        mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨univ ×ˢ Iio T, hV, hsub⟩
      have h₁s : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun q : ℝ × ℝ => c₁.lift q.1 q.2)
          (univ ×ˢ Icc a T) (x, t) :=
        h₁.smooth (x, t) ⟨mem_univ _, hp.2.1, le_of_lt hlt⟩
      have hVT : (univ ×ˢ Iio T) ∈ 𝓝[univ ×ˢ Icc a u] (x, t) :=
        mem_nhdsWithin_iff_eventually.mpr (by filter_upwards [hV] with q hq _; exact hq)
      refine (h₁s.mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [hVT] with q hq
        exact heq₁ q.1 q.2 (le_of_lt hq.2)
      · exact heq₁ x t (le_of_lt hlt)
    · have htT : t₀ < t := by rw [heq]; exact ht₀T
      have htu : t < u := by rw [heq]; exact hTu
      have hmemU : (univ ×ˢ Icc t₀ u) ∈ 𝓝 (x, t) :=
        mem_of_superset
          ((isOpen_univ.prod isOpen_Ioo).mem_nhds
            (by simp only [Set.mem_prod, mem_univ, true_and, Set.mem_Ioo]
                exact ⟨htT, htu⟩))
          (Set.prod_mono Subset.rfl Ioo_subset_Icc_self)
      have hV : (univ : Set ℝ) ×ˢ Ioi t₀ ∈ 𝓝 (x, t) :=
        (isOpen_univ.prod isOpen_Ioi).mem_nhds
          (by simp only [Set.mem_prod, mem_univ, true_and, Set.mem_Ioi]; exact htT)
      have h₂s : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun q : ℝ × ℝ => c₂.lift q.1 q.2)
          (univ ×ˢ Icc t₀ u) (x, t) :=
        h₂.smooth (x, t) ⟨mem_univ _, le_of_lt htT, le_of_lt htu⟩
      have hevAt : (fun q : ℝ × ℝ => cJ.lift q.1 q.2) =ᶠ[𝓝 (x, t)]
          (fun q : ℝ × ℝ => c₂.lift q.1 q.2) := by
        filter_upwards [hV] with q hq
        exact heq₂ q.1 q.2 hq.2
      exact ((h₂s.contMDiffAt hmemU).congr_of_eventuallyEq hevAt).contMDiffWithinAt
    · have ht₀t : t₀ < t := lt_trans ht₀T hgt
      have hV : (univ : Set ℝ) ×ˢ Ioi T ∈ 𝓝 (x, t) :=
        (isOpen_univ.prod isOpen_Ioi).mem_nhds
          (by simp only [Set.mem_prod, mem_univ, true_and, Set.mem_Ioi]; exact hgt)
      have hsub : ((univ : Set ℝ) ×ˢ Ioi T) ∩ (univ ×ˢ Icc a u) ⊆
          univ ×ˢ Icc t₀ u := by
        rintro ⟨y, s⟩ ⟨⟨-, hs⟩, ⟨-, hsa, hsu⟩⟩
        exact ⟨mem_univ _, le_of_lt (lt_trans ht₀T hs), hsu⟩
      have hmem : (univ ×ˢ Icc t₀ u) ∈ 𝓝[univ ×ˢ Icc a u] (x, t) :=
        mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨univ ×ˢ Ioi T, hV, hsub⟩
      have h₂s : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun q : ℝ × ℝ => c₂.lift q.1 q.2)
          (univ ×ˢ Icc t₀ u) (x, t) :=
        h₂.smooth (x, t) ⟨mem_univ _, le_of_lt ht₀t, hp.2.2⟩
      have hVT : (univ ×ˢ Ioi T) ∈ 𝓝[univ ×ˢ Icc a u] (x, t) :=
        mem_nhdsWithin_iff_eventually.mpr (by filter_upwards [hV] with q hq _; exact hq)
      refine (h₂s.mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [hVT] with q hq
        exact heq₂ q.1 q.2 (lt_trans ht₀T hq.2)
      · exact heq₂ x t (lt_trans ht₀T hgt)
  · intro x t ht
    rcases lt_trichotomy t T with hlt | heq | hgt
    · rw [X_congr (I := I) (c := cJ) (d := c₁) (fun z => heq₁ z t (le_of_lt hlt)) x]
      exact h₁.immersed x t ⟨ht.1, le_of_lt hlt⟩
    · have ht₁ : a ≤ T := heq ▸ ht.1
      rw [heq]
      rw [X_congr (I := I) (c := cJ) (d := c₁) (fun z => heq₁ z T le_rfl) x]
      exact h₁.immersed x T ⟨ht₁, le_rfl⟩
    · have ht₀t : t₀ < t := lt_trans ht₀T hgt
      rw [X_congr (I := I) (c := cJ) (d := c₂) (fun z => heq₂ z t ht₀t) x]
      exact h₂.immersed x t ⟨le_of_lt ht₀t, ht.2⟩
  · intro x t ht
    rcases lt_trichotomy t T with hlt | heq | hgt
    · have hset : Icc a u =ᶠ[𝓝 t] Icc a T := by
        rw [Filter.eventuallyEq_set]
        filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
        exact ⟨fun h => ⟨h.1, le_of_lt hs⟩, fun h => ⟨h.1, le_trans h.2 hTu.le⟩⟩
      have hev : (cJ.lift x) =ᶠ[𝓝[Icc a u] t] (c₁.lift x) := by
        filter_upwards [mem_nhdsWithin_iff_eventually.mpr
          (by filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs _; exact hs)] with s hs
        exact heq₁ x s (le_of_lt hs)
      have hA : mfderivWithin 𝓘(ℝ, ℝ) I (cJ.lift x) (Icc a u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₁.lift x) (Icc a u) t :=
        hev.mfderivWithin_eq (heq₁ x t (le_of_lt hlt))
      have hB : mfderivWithin 𝓘(ℝ, ℝ) I (c₁.lift x) (Icc a u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₁.lift x) (Icc a T) t :=
        mfderivWithin_congr_set hset
      have hvel : cJ.velocity (I := I) (Icc a u) x t = c₁.velocity (I := I) (Icc a T) x t := by
        unfold CurveMap.velocity
        rw [hA, hB]
        rfl
      rw [hvel, h₁.equation x t ⟨ht.1, le_of_lt hlt⟩]
      exact (curvatureVector_congr (c := cJ) (d := c₁) (g := g) (t := t)
        (fun z => heq₁ z t (le_of_lt hlt)) x).symm
    · have htT : t₀ < t := by rw [heq]; exact ht₀T
      have htu : t < u := by rw [heq]; exact hTu
      have hat : max a t₀ < t := by rw [max_eq_right hat₀]; exact htT
      have hset : Icc a u =ᶠ[𝓝 t] Icc t₀ u := by
        rw [Filter.eventuallyEq_set]
        filter_upwards [isOpen_Ioo.mem_nhds ⟨hat, htu⟩] with s hs
        exact ⟨fun _ => ⟨le_of_lt (lt_of_le_of_lt (le_max_right a t₀) hs.1), hs.2.le⟩,
          fun _ => ⟨le_trans hat₀ (le_of_lt (lt_of_le_of_lt (le_max_right a t₀) hs.1)), hs.2.le⟩⟩
      have hev : (cJ.lift x) =ᶠ[𝓝[Icc a u] t] (c₂.lift x) := by
        filter_upwards [mem_nhdsWithin_iff_eventually.mpr
          (by filter_upwards [isOpen_Ioi.mem_nhds htT] with s hs _; exact hs)] with s hs
        exact heq₂ x s hs
      have hA : mfderivWithin 𝓘(ℝ, ℝ) I (cJ.lift x) (Icc a u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc a u) t :=
        hev.mfderivWithin_eq (heq₂ x t htT)
      have hB : mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc t₀ u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc a u) t :=
        mfderivWithin_congr_set hset.symm
      have hvel : cJ.velocity (I := I) (Icc a u) x t = c₂.velocity (I := I) (Icc t₀ u) x t := by
        unfold CurveMap.velocity
        rw [hA, hB]
        rfl
      rw [hvel, h₂.equation x t ⟨le_of_lt htT, le_of_lt htu⟩]
      exact (curvatureVector_congr (c := cJ) (d := c₂) (g := g) (t := t)
        (fun z => heq₂ z t htT) x).symm
    · have ht₀t : t₀ < t := lt_trans ht₀T hgt
      have hset : Icc a u =ᶠ[𝓝 t] Icc t₀ u := by
        rw [Filter.eventuallyEq_set]
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
        exact ⟨fun h => ⟨le_of_lt (lt_trans ht₀T hs), h.2⟩,
          fun h => ⟨le_trans hat₀ (le_of_lt (lt_trans ht₀T hs)), h.2⟩⟩
      have hev : (cJ.lift x) =ᶠ[𝓝[Icc a u] t] (c₂.lift x) := by
        filter_upwards [mem_nhdsWithin_iff_eventually.mpr
          (by filter_upwards [isOpen_Ioi.mem_nhds ht₀t] with s hs _; exact hs)] with s hs
        exact heq₂ x s hs
      have hA : mfderivWithin 𝓘(ℝ, ℝ) I (cJ.lift x) (Icc a u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc a u) t :=
        hev.mfderivWithin_eq (heq₂ x t ht₀t)
      have hB : mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc t₀ u) t =
          mfderivWithin 𝓘(ℝ, ℝ) I (c₂.lift x) (Icc a u) t :=
        mfderivWithin_congr_set hset.symm
      have hvel : cJ.velocity (I := I) (Icc a u) x t = c₂.velocity (I := I) (Icc t₀ u) x t := by
        unfold CurveMap.velocity
        rw [hA, hB]
        rfl
      rw [hvel, h₂.equation x t ⟨le_of_lt ht₀t, ht.2⟩]
      exact (curvatureVector_congr (c := cJ) (d := c₂) (g := g) (t := t)
        (fun z => heq₂ z t ht₀t) x).symm

omit [CompleteSpace E] in
theorem tendsto_slice_of_terminalClosure {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a T : ℝ} (haT : a < T) {g : ℝ → SmoothRiemannianMetric I M}
    {c closed : CurveMap M}
    (hsol : CurveMap.IsSolutionOn (I := I) closed g (Icc a T))
    (hagr : ∀ z t, t ∈ Ico a T → closed z t = c z t)
    (hc : c.SmoothOn (I := I) (Ico a T)) (hi : c.ImmersedOn (I := I) (Ico a T)) :
    letI := smoothImmersionTopology e
    Tendsto
      (fun t : {t : ℝ // t ∈ Ico a T} => SmoothImmersion.slice c hc hi t.1 t.2)
      (Filter.comap Subtype.val (𝓝[<] T))
      (𝓝 (SmoothImmersion.slice closed hsol.smooth hsol.immersed T ⟨haT.le, le_rfl⟩)) := by
  set cT : SmoothImmersion (I := I) (M := M) :=
    SmoothImmersion.slice closed hsol.smooth hsol.immersed T ⟨haT.le, le_rfl⟩ with hcT
  rw [TopologicalSpace.tendsto_nhds_generateFrom_iff]
  rintro V ⟨d₀, m, ε, hε, rfl⟩ hV
  have hcontT : ContinuousOn (fun x : ℝ => iteratedDeriv m
      (fun y : ℝ => e.map (cT.map (y : AddCircle (1 : ℝ)))) x) (Icc (0 : ℝ) 1) :=
    continuousOn_iteratedDeriv_embedding e cT m
  have hcont₀ : ContinuousOn (fun x : ℝ => iteratedDeriv m
      (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x) (Icc (0 : ℝ) 1) :=
    continuousOn_iteratedDeriv_embedding e d₀ m
  have hgap : ContinuousOn (fun x : ℝ => ε -
      ‖iteratedDeriv m (fun y : ℝ => e.map (cT.map (y : AddCircle (1 : ℝ)))) x -
        iteratedDeriv m (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x‖)
      (Icc (0 : ℝ) 1) :=
    continuousOn_const.sub (hcontT.sub hcont₀).norm
  obtain ⟨η, hηpos, hη⟩ := exists_pos_le_of_continuousOn_pos hgap
    (fun x hx => sub_pos.mpr (hV x hx))
  obtain ⟨δ, hδpos, hδb⟩ := exists_nhds_slice_jet_variation e haT hsol.smooth m
    ⟨haT.le, le_rfl⟩ (by linarith : (0 : ℝ) < η / 2)
  have hminpos : 0 < min δ (T - a) := lt_min hδpos (by linarith)
  have hmem : Ioo (T - min δ (T - a)) T ∈ 𝓝[<] T :=
    mem_nhdsWithin_iff_eventually.mpr (by
      filter_upwards [isOpen_Ioi.mem_nhds (by linarith [hminpos] : T - min δ (T - a) < T)]
        with t ht htlt
      exact ⟨ht, htlt⟩)
  refine Filter.mem_comap.mpr ⟨Ioo (T - min δ (T - a)) T, hmem, ?_⟩
  rintro ⟨t, ht⟩ htI
  intro x hx
  simp only [SmoothImmersion.slice]
  have hdist : |t - T| < δ := by
    rw [abs_of_neg (by linarith [htI.2] : t - T < 0)]
    have : t > T - min δ (T - a) := htI.1
    linarith [min_le_left δ (T - a)]
  have hjet : (fun y : ℝ => e.map (c (y : AddCircle (1 : ℝ)) t)) =
      (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) :=
    funext (fun y => congrArg e.map ((hagr (y : AddCircle (1 : ℝ)) t ht).symm))
  rw [hjet]
  have hcomp_t : iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) x =
      (iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (closed.lift q.1 q.2))
        (univ ×ˢ Icc a T) (x, t)) (fun _ : Fin m => (1, 0)) := by
    simpa only [CurveMap.lift] using
      slice_jet_eq_jet_component e haT hsol.smooth m ⟨ht.1, le_of_lt ht.2⟩
  have hcomp_T : iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x =
      (iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (closed.lift q.1 q.2))
        (univ ×ˢ Icc a T) (x, T)) (fun _ : Fin m => (1, 0)) := by
    simpa only [CurveMap.lift] using
      slice_jet_eq_jet_component e haT hsol.smooth m ⟨haT.le, le_rfl⟩
  have h1 : ‖iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) x -
      iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x‖ < η / 2 :=
    (by
      rw [hcomp_t, hcomp_T]
      exact
        hδb t ⟨ht.1, le_of_lt ht.2⟩ hdist x hx)
  have h2 : ‖iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x -
      iteratedDeriv m (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x‖ ≤ ε - η :=
    (by
      have h := hη x hx
      simp only [hcT, SmoothImmersion.slice] at h
      linarith)
  have htri : ‖iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) x -
        iteratedDeriv m (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x‖ ≤
      ‖iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) x -
        iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x‖ +
      ‖iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x -
        iteratedDeriv m (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) t)) x)
      (iteratedDeriv m (fun y : ℝ => e.map (closed (y : AddCircle (1 : ℝ)) T)) x)
      (iteratedDeriv m (fun y : ℝ => e.map (d₀.map (y : AddCircle (1 : ℝ)))) x)
  linarith

end CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M]
  [nonemptyM : Nonempty M] [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

def curveShorteningLocalWindow (B : SmoothMetricWindow (I := I) (M := M) D a b) : Prop :=
  ∀ (t₀ : {t : ℝ // t ∈ Ico a b}) (c₀ : SmoothImmersion (I := I) (M := M))
    (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
    letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ τ > 0, ∃ U : Set ({t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ (t₀, c₀) ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a b)) solutions) ∧
        ∀ p : U, (p.1.1 : ℝ) + τ ≤ b ∧
          CurveMap.IsSolutionOn (I := I) (solutions p) B.family.metric
            (Icc (p.1.1 : ℝ) ((p.1.1 : ℝ) + τ)) ∧
          ∀ z, solutions p z (p.1.1 : ℝ) = p.1.2.map z

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem exists_extension_of_localWindow
    (B : SmoothMetricWindow (I := I) (M := M) D a b) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {T : ℝ} (haT : a < T) (hTb : T < b) {c : CurveMap M}
    (hc : CurveMap.IsSolutionOn (I := I) c B.family.metric (Ico a T))
    (hclose : ∃ closed : CurveMap M,
      CurveMap.IsSolutionOn (I := I) closed B.family.metric (Icc a T) ∧
      ∀ z t, t ∈ Ico a T → closed z t = c z t)
    (hwin : curveShorteningLocalWindow (I := I) (M := M) B)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B) :
    ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : CurveMap M,
      CurveMap.IsSolutionOn (I := I) extended B.family.metric (Icc a (T + τ)) ∧
      ∀ z t, t ∈ Ico a T → extended z t = c z t :=
  letI instImm : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  by
  classical
  obtain ⟨closed, hsol, hagr⟩ := hclose
  let cT : SmoothImmersion (I := I) (M := M) :=
    SmoothImmersion.slice closed hsol.smooth hsol.immersed T ⟨haT.le, le_rfl⟩
  let t₀ : {t : ℝ // t ∈ Ico a b} := ⟨T, haT.le, hTb⟩
  obtain ⟨τ, hτpos, U, hUopen, hmemU, sols, hcont, hprop⟩ := hwin t₀ cT N e
  have htend : Tendsto (fun t : {t : ℝ // t ∈ Ico a T} =>
      SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2)
      (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 cT) :=
    CurveMap.tendsto_slice_of_terminalClosure e haT hsol hagr hc.smooth hc.immersed
  have hfirst : Tendsto (fun t : {t : ℝ // t ∈ Ico a T} =>
      (⟨t.1, ⟨t.2.1, lt_trans t.2.2 hTb⟩⟩ : {t : ℝ // t ∈ Ico a b}))
      (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 t₀) := by
    rw [nhds_subtype]
    rw [tendsto_comap_iff]
    exact Filter.tendsto_comap.mono_right nhdsWithin_le_nhds
  have hprod : Tendsto (fun t : {t : ℝ // t ∈ Ico a T} =>
      ((⟨t.1, ⟨t.2.1, lt_trans t.2.2 hTb⟩⟩ : {t : ℝ // t ∈ Ico a b}),
        SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2))
      (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 (t₀, cT)) := by
    rw [nhds_prod_eq]
    exact hfirst.prodMk htend
  have hevent : ∀ᶠ t in Filter.comap Subtype.val (𝓝[<] T),
      ((⟨t.1, ⟨t.2.1, lt_trans t.2.2 hTb⟩⟩ : {t : ℝ // t ∈ Ico a b}),
        SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2) ∈ U :=
    hprod.eventually (hUopen.mem_nhds hmemU)
  obtain ⟨A, hA, hAsub⟩ := Filter.mem_comap.mp hevent
  obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hA
  obtain ⟨ε, hεpos, hεball⟩ := Metric.mem_nhds_iff.mp hV
  set ρ : ℝ := min (min ε τ) (T - a) with hρ
  have hρpos : 0 < ρ := by
    rw [hρ]
    exact lt_min (lt_min hεpos hτpos) (by linarith)
  have hρε : ρ / 3 < ε := by
    have h1 : ρ ≤ ε := by
      rw [hρ]
      exact (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hρτ : ρ / 3 < τ := by
    have h1 : ρ ≤ τ := by
      rw [hρ]
      exact (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hρa : ρ / 3 < T - a := by
    have h1 : ρ ≤ T - a := by rw [hρ]; exact min_le_right _ _
    linarith
  have ht'mem : T - ρ / 3 ∈ Ico a T := ⟨by linarith, by linarith⟩
  set t' : {t : ℝ // t ∈ Ico a T} := ⟨T - ρ / 3, ht'mem⟩ with ht'def
  have ht'val : (t' : ℝ) = T - ρ / 3 := rfl
  have ht'ltT : (t' : ℝ) < T := by
    rw [ht'val]
    linarith [hρpos]
  have ht'ball : |(t' : ℝ) - T| < ε := by
    have hsubρ : T - ρ / 3 - T = -(ρ / 3) := by ring
    rw [ht'val, hsubρ, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < ρ / 3)]
    exact hρε
  have ht'A : (t' : ℝ) ∈ A := hVsub ⟨hεball ht'ball, ht'ltT⟩
  have hmemUt' : ((⟨(t' : ℝ), ⟨t'.2.1, lt_trans t'.2.2 hTb⟩⟩ : {t : ℝ // t ∈ Ico a b}),
      SmoothImmersion.slice c hc.smooth hc.immersed (t' : ℝ) t'.2) ∈ U :=
    hAsub ht'A
  obtain ⟨hτb, hsolU, hinitU⟩ := hprop ⟨_, hmemUt'⟩
  have hmin : min T ((t' : ℝ) + τ) = T := by
    rw [min_eq_left_iff, ht'val]
    linarith
  have hagree : ∀ z t, t ∈ Icc (t' : ℝ) T →
      closed z t = sols ⟨_, hmemUt'⟩ z t := by
    intro z t ht
    refine huniq (t' : ℝ) T ((t' : ℝ) + τ) t'.2.1 ht'ltT (by linarith)
      hTb.le hτb closed
      (sols ⟨_, hmemUt'⟩)
      (hsol.mono_Icc t'.2.1 le_rfl ht'ltT) hsolU ?_ z t ?_
    · intro z'
      have h1 : closed z' (t' : ℝ) = c z' (t' : ℝ) := hagr z' (t' : ℝ) t'.2
      have h2 : sols ⟨_, hmemUt'⟩ z' (t' : ℝ) =
          (SmoothImmersion.slice c hc.smooth hc.immersed (t' : ℝ) t'.2).map z' := hinitU z'
      rw [h1, h2]
      rfl
    · rw [hmin]
      exact ht
  have hglue : CurveMap.IsSolutionOn (I := I)
      (fun z t => if t ≤ T then closed z t else sols ⟨_, hmemUt'⟩ z t)
      B.family.metric (Icc a ((t' : ℝ) + τ)) :=
    CurveMap.IsSolutionOn.glue (g := B.family.metric) t'.2.1 ht'ltT
      (by linarith) hsol hsolU hagree
  have hhorizon : T + (τ - ρ / 3) = (t' : ℝ) + τ := by
    rw [ht'val]
    ring
  refine ⟨τ - ρ / 3, by linarith, ?_, ?_⟩
  · rw [ht'val] at hτb
    linarith
  · refine ⟨fun z t => if t ≤ T then closed z t else sols ⟨_, hmemUt'⟩ z t, ?_, ?_⟩
    · rw [hhorizon]
      exact hglue
    · intro z t ht
      simp only [if_pos (le_of_lt ht.2)]
      exact hagr z t ht

def curveShorteningTerminalClosure (B : RicciBackground (I := I) (M := M) D a b) : Prop :=
  ∀ (T : ℝ), a < T → T ≤ b → ∀ (c : CurveMap M) (K : ℝ), 0 ≤ K →
    CurveMap.IsSolutionOn (I := I) c B.family.metric (Ico a T) →
    (∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) →
    ∃ closed : CurveMap M,
      CurveMap.IsSolutionOn (I := I) closed B.family.metric (Icc a T) ∧
      ∀ z t, t ∈ Ico a T → closed z t = c z t

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem rfs_csf_continuation_of_terminalClosure
    (B : RicciBackground (I := I) (M := M) D a b) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (c : CurveMap M) (hc : CurveMap.IsSolutionOn (I := I) c B.family.metric (Ico a T))
    (K : ℝ) (hK : 0 ≤ K)
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    (hclose : curveShorteningTerminalClosure (I := I) (M := M) B)
    (hwin : curveShorteningLocalWindow (I := I) (M := M) B.toSmoothMetricWindow)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B.toSmoothMetricWindow) :
    ∃ cT : SmoothImmersion (I := I) (M := M),
      (∀ (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
        letI := smoothImmersionTopology e
        Tendsto
          (fun t : {t : ℝ // t ∈ Ico a T} => SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2)
          (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 cT)) ∧
      (∃ closed : CurveMap M, closed.IsSolutionOn B.family.metric (Icc a T) ∧
        (∀ z t, t ∈ Ico a T → closed z t = c z t) ∧ (∀ z, closed z T = cT.map z)) ∧
      (T < b → ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : CurveMap M,
        extended.IsSolutionOn B.family.metric (Icc a (T + τ)) ∧
        (∀ z t, t ∈ Ico a T → extended z t = c z t)) := by
  obtain ⟨closed, hsol, hagr⟩ := hclose T haT hTb c K hK hc hcurv
  refine ⟨SmoothImmersion.slice closed hsol.smooth hsol.immersed T ⟨haT.le, le_rfl⟩, ?_,
    ⟨closed, hsol, hagr, fun z => rfl⟩, ?_⟩
  · intro N' e'
    exact CurveMap.tendsto_slice_of_terminalClosure e' haT hsol hagr hc.smooth hc.immersed
  · intro hTb'
    exact exists_extension_of_localWindow B.toSmoothMetricWindow e haT hTb' hc
      ⟨closed, hsol, hagr⟩ hwin huniq
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
