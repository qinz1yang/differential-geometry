import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoverRegularAssembly_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventRightFamily_S38
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyThickCores_S37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PersistSame_O33

set_option autoImplicit false

/-! CH12-O33 G2 (R4e) — event-time cover by the same-point persistence route (lead ruling).
At an event time `a`: S38 right family `(Q, G)`; the point `q` stays `(w'/2)`-thick at the same
point for `t ↓ a` (`hpersist_same_O33`); every such `t` near `a` is regular (S38 gap), so the
regular cover (`cover_regular_of_done_O27` at `w/2`) puts `q` in some core image; a fixed index
occurs for arbitrarily small `t - a` (`exists_frequent_index_O33`); the right-limit pull-back
`hlim` ([FROZEN] CH12-O33 G2 addendum) gives `q` in the image at time `a`; the radius `w'⁻¹`
follows from `hpi07_thick_transfer_O27` at time `a`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- Thickness in a family metric on the stage `Q` of a regular slice, read in the slice. -/
theorem thick_slice_of_family_O33 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (s : RegularSlice F.observation) {Q : OrientedThreeStage.{u}}
    (hst : s.stage = Q) (m : Q.Metric) (hm : HEq s.metric m) (q : Q.Carrier) (w ρ : ℝ)
    (hc : curvatureRadius (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive) m) q = ENNReal.ofReal ρ)
    (hv : ENNReal.ofReal (w * ρ ^ 3) ≤
      ballVolume (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive) m) q ρ) :
    curvatureRadius s.normalizedMetric
        (cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hst.symm) q) =
        ENNReal.ofReal ρ ∧
      ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.normalizedMetric
        (cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hst.symm) q) ρ := by
  subst hst
  obtain rfl := eq_of_heq hm
  exact ⟨hc, hv⟩

/-- `sliceCast` equation, transported to the common stage `Q`. -/
theorem cast_eq_of_sliceCast_O33 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (s : RegularSlice F.observation) {Q : OrientedThreeStage.{u}}
    (hst : s.stage = Q) (x : (postStage F.observation s.time).Carrier) (q : Q.Carrier)
    (h : sliceCast_CX4 s x =
      cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hst.symm) q) :
    cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier)
      ((postStage_eq_sliceStage_CX4 s).trans hst)) x = q := by
  subst hst
  unfold sliceCast_CX4 at h
  simpa using h

/-- Finite pigeonhole for a property monotone in `δ`. -/
theorem exists_frequent_index_O33 {n : ℕ} (Pr : Fin n → ℝ → Prop)
    (hmono : ∀ i δ δ', δ ≤ δ' → Pr i δ → Pr i δ')
    (h : ∀ δ : ℝ, 0 < δ → ∃ i, Pr i δ) : ∃ i, ∀ δ : ℝ, 0 < δ → Pr i δ := by
  by_contra hcon
  push Not at hcon
  choose δ hδ hP using hcon
  have hsum0 : 0 ≤ ∑ i, (δ i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.mpr (hδ i)).le
  have hmle : ∀ i, (1 + ∑ i, (δ i)⁻¹)⁻¹ ≤ δ i := fun i => by
    have h1 : (δ i)⁻¹ ≤ 1 + ∑ i, (δ i)⁻¹ := by
      have := Finset.single_le_sum (f := fun i => (δ i)⁻¹)
        (fun j _ => (inv_pos.mpr (hδ j)).le) (Finset.mem_univ i)
      linarith
    simpa using inv_anti₀ (inv_pos.mpr (hδ i)) h1
  obtain ⟨i, hi⟩ := h ((1 + ∑ i, (δ i)⁻¹)⁻¹) (inv_pos.mpr (by linarith))
  exact hP i (hmono i _ (δ i) (hmle i) hi)

/-- **R4e, event times** ([FROZEN] CH12-O33 G2 conclusion), from the regular-time data and the
right-limit pull-back `hlim` ([FROZEN] CH12-O33 G2 addendum). -/
theorem cover_event_of_lim_O33 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K count : ℕ)
    (model : Fin count → FiniteVolumeHyperbolicModel.{u}) (Tr : ∀ i, HyperbolicTruncation (model i))
    (start : Fin count → ℝ) (α : Fin count → ℝ → ℝ)
    (Ω : ∀ i, TopologicalSpace.Opens (ℝ × (model i).Carrier))
    (map : ∀ i (t : ℝ), start i ≤ t → (model i).Carrier → (postStage F.observation t).Carrier)
    (hstart : ∀ i, 0 < start i) (hpos : ∀ i t, start i ≤ t → 0 < α i t)
    (hdecay : ∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α i t < ε)
    (hsmooth : ∀ i t (ht : start i ≤ t),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (sourceSlice_CX5 (Ω i) t))
    (hemb : ∀ i t (ht : start i ≤ t), IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
      (fun x : sourceSlice_CX5 (Ω i) t => map i t ht x))
    (hball : ∀ i t, start i ≤ t → riemannianBallOf (model i).metric (model i).basepoint
      (2 * (α i t)⁻¹) ⊆ sourceSlice_CX5 (Ω i) t)
    (hck : ∀ i t (ht : start i ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α i t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf (model i).metric (model i).basepoint (2 * (α i t)⁻¹),
        ckErr_O21 (model i) (postMetric F.observation t) t⁻¹ (map i t ht) k p < α i t)
    (hDone : ∀ w : ℝ, 0 < w → ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
      ¬ ∀ (i : Fin count) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : start i ≤ (S.slices j).time,
        S.point j ∉ sliceCast_CX4 (S.slices j) ''
          (map i _ hj '' riemannianBallOf (model i).metric (model i).basepoint R))
    (hlim : ∀ (i : Fin count) (a : ℝ) (ha : start i ≤ a) (Q : OrientedThreeStage.{u})
      (hQa : postStage F.observation a = Q) (N : ℝ), N + 1 < (α i a)⁻¹ → ∀ q : Q.Carrier,
      (∀ δ : ℝ, 0 < δ → ∃ (t : ℝ) (ht : start i ≤ t) (hQt : postStage F.observation t = Q),
        a < t ∧ t ≤ a + δ ∧ ∃ y ∈ riemannianBallOf (model i).metric (model i).basepoint N,
          cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hQt) (map i t ht y) = q) →
      ∃ y ∈ riemannianBallOf (model i).metric (model i).basepoint (N + 1),
        cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hQa) (map i a ha y) = q) :
    ∃ w0 : ℝ, 0 < w0 ∧ ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ (t : ℝ) (ht0 : 0 < t), T ≤ t →
      t ∈ F.observation.eventTimes → ∀ w' : ℝ, w ≤ w' → w' ≤ w0 →
        ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
          curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p =
            ENNReal.ofReal r →
          ENNReal.ofReal (w' * r ^ 3) ≤
            ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht0) (postMetric F.observation t)) p r →
          ∃ (i : Fin count) (hi : start i ≤ t),
            p ∈ map i t hi '' riemannianBallOf (model i).metric (model i).basepoint w'⁻¹ := by
  choose w0 hw0 Tg hG using fun i => hpi07_thick_transfer_O27 F K (model i) (Tr i) (start i)
    (hstart i) (α i) (Ω i) (map i) (hpos i) (hdecay i) (hemb i) (hsmooth i) (hball i) (hck i)
  have hsum0 : 0 ≤ ∑ i, (w0 i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.mpr (hw0 i)).le
  refine ⟨(1 + ∑ i, (w0 i)⁻¹)⁻¹, by positivity, fun w hw => ?_⟩
  have hw0le : ∀ i, (1 + ∑ i, (w0 i)⁻¹)⁻¹ ≤ w0 i := fun i => by
    have h1 : (w0 i)⁻¹ ≤ 1 + ∑ i, (w0 i)⁻¹ := by
      have := Finset.single_le_sum (f := fun i => (w0 i)⁻¹)
        (fun j _ => (inv_pos.mpr (hw0 j)).le) (Finset.mem_univ i)
      linarith
    simpa using inv_anti₀ (inv_pos.mpr (hw0 i)) h1
  obtain ⟨N, T₀, hcov⟩ := cover_regular_of_done_O27 F count model start map (w / 2)
    (hDone (w / 2) (half_pos hw))
  choose Td hTd using fun i => hdecay i (1 / ((N : ℝ) + 2)) (by positivity)
  refine ⟨max T₀ (∑ i, (|Tg i| + |Td i| + |start i|)),
    fun a ha0 hT hev w' hww' hw'0 p r hr hcr hth => ?_⟩
  have hTi : ∀ i, |Tg i| + |Td i| + |start i| ≤ a := fun i =>
    (Finset.single_le_sum (f := fun i => |Tg i| + |Td i| + |start i|) (fun j _ => by positivity)
      (Finset.mem_univ i)).trans ((le_max_right _ _).trans hT)
  have hsa : ∀ i, start i ≤ a := fun i => (le_abs_self _).trans
    (by linarith [abs_nonneg (Tg i), abs_nonneg (Td i), hTi i])
  have hw'pos : 0 < w' := hw.trans_le hww'
  have hT₀a : T₀ ≤ a := (le_max_left _ _).trans hT
  -- the right family at the event time `a`
  obtain ⟨Q, G, ε0, hε0, hsm, hQ, hpost, hslices⟩ := exists_smooth_right_family_S38 F.observation hev
  obtain ⟨hcrq, hthq⟩ := thick_cast_of_post_O27 F a hQ (G a) hpost (inv_pos.mpr ha0) p w' r hcr hth
  obtain ⟨q, hq⟩ : ∃ q : Q.Carrier,
      q = cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hQ) p := ⟨_, rfl⟩
  rw [← hq] at hcrq hthq
  obtain ⟨ε1, hε1, hpers⟩ := hpersist_same_O33 Q G a ε0 ha0 hε0 hsm w' hw'pos q r hr hcrq hthq
  obtain ⟨ε2, hε2, -, hgap⟩ := exists_eventFree_gap_S38 F.observation (te := a)
  -- for every `δ > 0`, `q` lies in a core image at some regular time in `(a, a + δ]`
  have hfreq : ∀ δ : ℝ, 0 < δ → ∃ i, ∃ (t : ℝ) (ht : start i ≤ t)
      (hQt : postStage F.observation t = Q), a < t ∧ t ≤ a + δ ∧
        ∃ y ∈ riemannianBallOf (model i).metric (model i).basepoint N,
          cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hQt) (map i t ht y) = q := by
    intro δ hδ
    have hm0 : 0 < min (min δ ε0) (min ε1 ε2) := lt_min (lt_min hδ hε0) (lt_min hε1 hε2)
    have hmδ : min (min δ ε0) (min ε1 ε2) ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
    have hm0' : min (min δ ε0) (min ε1 ε2) ≤ ε0 := (min_le_left _ _).trans (min_le_right _ _)
    have hm1 : min (min δ ε0) (min ε1 ε2) ≤ ε1 := (min_le_right _ _).trans (min_le_left _ _)
    have hm2 : min (min δ ε0) (min ε1 ε2) ≤ ε2 := (min_le_right _ _).trans (min_le_right _ _)
    have hnot : a + min (min δ ε0) (min ε1 ε2) ∉ F.observation.eventTimes := fun hmem =>
      hgap _ hmem (by linarith) (by linarith)
    obtain ⟨s, hs⟩ := regularSlice_exists_of_not_eventTime_S37 F.observation _ (by linarith) hnot
    have hs1 : a < s.time := by rw [hs]; linarith
    obtain ⟨hst, hsmet⟩ := hslices s hs1 (by rw [hs]; linarith)
    obtain ⟨ρ, hρ, hc, hv⟩ := hpers s.time hs1 (by rw [hs]; linarith)
    obtain ⟨hc', hv'⟩ := thick_slice_of_family_O33 F s hst (G s.time) hsmet q (w' / 2) ρ hc hv
    have hv'' : ENNReal.ofReal (w / 2 * ρ ^ 3) ≤ ballVolume s.normalizedMetric
        (cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hst.symm) q) ρ :=
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (by positivity))).trans hv'
    obtain ⟨i, hi, x, ⟨y, hy, rfl⟩, hx⟩ := hcov s (hT₀a.trans hs1.le) _ ρ hρ hc' hv''
    exact ⟨i, s.time, hi, (postStage_eq_sliceStage_CX4 s).trans hst, hs1,
      by rw [hs]; linarith, y, hy, cast_eq_of_sliceCast_O33 F s hst _ q hx⟩
  obtain ⟨i, hi⟩ := exists_frequent_index_O33 (fun i δ => ∃ (t : ℝ) (ht : start i ≤ t)
      (hQt : postStage F.observation t = Q), a < t ∧ t ≤ a + δ ∧
        ∃ y ∈ riemannianBallOf (model i).metric (model i).basepoint N,
          cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier) hQt) (map i t ht y) = q)
    (fun _ _ _ hδδ' ⟨t, ht, hQt, h1, h2, h3⟩ => ⟨t, ht, hQt, h1, h2.trans (by linarith), h3⟩) hfreq
  have hαa := hpos i a (hsa i)
  have hα1 : α i a < 1 / ((N : ℝ) + 2) := hTd i a ((le_abs_self _).trans
    (by linarith [abs_nonneg (Tg i), abs_nonneg (start i), hTi i]))
  have hαN : (N : ℝ) + 2 < (α i a)⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hαa]; simpa [one_div] using hα1
  obtain ⟨y, hy, hyq⟩ := hlim i a (hsa i) Q hQ N (by linarith) q hi
  rw [hq] at hyq
  have hyp : map i a (hsa i) y = p := (cast_inj _).1 hyq
  subst hyp
  refine ⟨i, hsa i, y, ?_, rfl⟩
  exact hG i a (hsa i) ((le_abs_self _).trans
      (by linarith [abs_nonneg (Td i), abs_nonneg (start i), hTi i])) w' hw'pos
    (hw'0.trans (hw0le i)) y (riemannianBallOf_mono _ _ (by linarith) hy) r hr hcr hth

end GC.LongTime.Ch12
