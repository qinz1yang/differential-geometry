import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Minimum.Monotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompactSublevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.TimeExtension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [TopologicalSpace.MetrizableSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_free_endpoint_minimizers_of_compact_linear_action_sublevels
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {b₀ b₁ : ℝ} (hb₀ : 0 < b₀)
    (hreg : Icc (T - b₁ ^ 2) T ⊆ D.regular)
    (x : M) (Q : Set M) (hQ : IsCompact Q)
    (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 α₀) (hα₀start : α₀ 0 = x)
    (hα₀act : lRegularizedAction S T α₀ 0 b₀ < (Module.finrank ℝ E : ℝ) * b₀)
    (hconf : ∀ b ∈ Icc b₀ b₁, ∀ α : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 α → α 0 = x →
      lRegularizedAction S T α 0 b < (Module.finrank ℝ E : ℝ) * b →
      MapsTo α (Icc 0 b) Q) :
    ∃ η : ℝ → ℝ → M, ∀ b ∈ Icc b₀ b₁,
      ContMDiff 𝓘(ℝ, ℝ) I 1 (η b) ∧ η b 0 = x ∧ MapsTo (η b) (Icc 0 b) Q ∧
      (∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = x →
        lRegularizedAction S T (η b) 0 b ≤ lRegularizedAction S T δ 0 b) ∧
      2 * b * lRegularizedAction S T (η b) 0 b - 2 * (Module.finrank ℝ E : ℝ) * b ^ 2 ≤
        2 * b₀ * lRegularizedAction S T α₀ 0 b₀ - 2 * (Module.finrank ℝ E : ℝ) * b₀ ^ 2 ∧
      2 * b * lRegularizedAction S T (η b) 0 b - 2 * (Module.finrank ℝ E : ℝ) * b ^ 2 < 0 := by
  classical
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  by_cases hband : b₀ ≤ b₁
  swap
  · exact ⟨fun _ _ => x, fun b hb => False.elim (hband (hb.1.trans hb.2))⟩
  let n : ℝ := Module.finrank ℝ E
  let q₀ : ℝ := 2 * b₀ * lRegularizedAction S T α₀ 0 b₀ - 2 * n * b₀ ^ 2
  have hq₀ : q₀ < 0 := by
    dsimp only [q₀, n]
    nlinarith [mul_pos hb₀ (sub_pos.mpr hα₀act)]
  have hslab {b : ℝ} (hb : b ∈ Icc b₀ b₁) : Icc (T - b ^ 2) T ⊆ D.regular := by
    intro t ht
    exact hreg ⟨(sub_le_sub_left (pow_le_pow_left₀ (hb₀.le.trans hb.1) hb.2 2) T).trans ht.1, ht.2⟩
  have hclock {b : ℝ} (hb : b ∈ Icc b₀ b₁) : ∀ t ∈ Icc 0 b, T - t ^ 2 ∈ D.regular := by
    intro t ht
    exact hslab hb ⟨sub_le_sub_left (pow_le_pow_left₀ ht.1 ht.2 2) T, sub_le_self _ (sq_nonneg t)⟩
  let Seed : ℝ → Prop := fun b => ∃ α : ℝ → M,
    ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧ α 0 = x ∧ lRegularizedAction S T α 0 b < n * b
  have hseed₀ : Seed b₀ := ⟨α₀, hα₀, hα₀start, hα₀act⟩
  have hminSeed (b : ℝ) (hb : b ∈ Icc b₀ b₁) (hs : Seed b) :
      ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η 0 = x ∧ MapsTo η (Icc 0 b) Q ∧
        ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = x →
          lRegularizedAction S T η 0 b ≤ lRegularizedAction S T δ 0 b := by
    obtain ⟨α, hα, hα0, hαact⟩ := hs
    exact exists_lRegularizedMinC1_free_endpoint_of_compact_action_sublevel
      S hS T (hb₀.trans_le hb.1) (hclock hb) x α hα hα0 Q hQ
      (fun β hβ hβ0 hact => hconf b hb β hβ hβ0 (hact.trans_lt hαact))
  have hbounded (b : ℝ) (hb : b ∈ Icc b₀ b₁) (hs : ∀ c ∈ Icc b₀ b, Seed c) :
      ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η 0 = x ∧ MapsTo η (Icc 0 b) Q ∧
        (∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = x →
          lRegularizedAction S T η 0 b ≤ lRegularizedAction S T δ 0 b) ∧
        2 * b * lRegularizedAction S T η 0 b - 2 * n * b ^ 2 ≤ q₀ := by
    have hfamily (c : ℝ) (hc : c ∈ Icc b₀ b) :=
      hminSeed c ⟨hc.1, hc.2.trans hb.2⟩ (hs c hc)
    choose η hη hη0 hηQ hηmin using hfamily
    let family : ℝ → ℝ → M := fun c => if hc : c ∈ Icc b₀ b then η c hc else fun _ => x
    have heq (c : ℝ) (hc : c ∈ Icc b₀ b) : family c = η c hc := dif_pos hc
    have hanti := antitoneOn_scaled_action_sub_dim_mul_sq_of_compact_free_endpoint_minimizers
      S hS T hb₀ (hslab hb) x family Q hQ
      (fun c hc => by rw [heq c hc]; exact hη c hc)
      (fun c hc => by rw [heq c hc]; exact hη0 c hc)
      (fun c hc => by rw [heq c hc]; exact hηQ c hc)
      (fun c hc => by rw [heq c hc]; exact hηmin c hc)
    have hb0 : b₀ ∈ Icc b₀ b := ⟨le_rfl, hb.1⟩
    have hbb : b ∈ Icc b₀ b := ⟨hb.1, le_rfl⟩
    have hstartBound := mul_le_mul_of_nonneg_left (hηmin b₀ hb0 α₀ hα₀ hα₀start)
      (by positivity : 0 ≤ 2 * b₀)
    refine ⟨η b hbb, hη b hbb, hη0 b hbb, hηQ b hbb, hηmin b hbb, ?_⟩
    have hh := hanti hb0 hbb hb.1
    dsimp only at hh
    rw [heq b hbb, heq b₀ hb0] at hh
    exact hh.trans (sub_le_sub_right hstartBound _)
  let P : Set ℝ := {b | ∀ c ∈ Icc b₀ b, Seed c}
  have hP0 : b₀ ∈ P := by
    intro c hc
    have heq : c = b₀ := le_antisymm hc.2 hc.1
    exact heq.symm ▸ hseed₀
  have hPclosed : IsClosed (P ∩ Icc b₀ b₁) := by
    apply IsSeqClosed.isClosed
    intro time t htime hlim
    have ht : t ∈ Icc b₀ b₁ := isClosed_Icc.mem_of_tendsto hlim
      (Eventually.of_forall fun k => (htime k).2)
    refine ⟨?_, ht⟩
    have hbefore (c : ℝ) (hc : c ∈ Ico b₀ t) : Seed c := by
      obtain ⟨k, hk⟩ := (hlim.eventually (Ioi_mem_nhds hc.2)).exists
      exact (htime k).1 c ⟨hc.1, hk.le⟩
    let times := fun k => min (time k) t
    have htimes (k : ℕ) : times k ∈ Icc b₀ t :=
      ⟨le_min (htime k).2.1 ht.1, min_le_right _ _⟩
    have htimesBand (k : ℕ) : times k ∈ Icc b₀ b₁ :=
      ⟨(htimes k).1, (htimes k).2.trans ht.2⟩
    have htimesPrefix (k : ℕ) : ∀ c ∈ Icc b₀ (times k), Seed c := by
      intro c hc
      exact (htime k).1 c ⟨hc.1, hc.2.trans (min_le_left _ _)⟩
    choose η hη hη0 hηQ hηmin hηbound using
      fun k => hbounded (times k) (htimesBand k) (htimesPrefix k)
    have htimesLim : Tendsto times atTop (𝓝 t) := by
      simpa only [min_self] using hlim.min
        (show Tendsto (fun _ : ℕ => t) atTop (𝓝 t) from tendsto_const_nhds)
    obtain ⟨_, γ, hγ, hγ0, _, hγact⟩ := exists_lRegularizedAction_lt_linear_of_tendsto_time
      S hS.smoothMetric ⟨hS.scalarCont⟩ T t Q hQ
      (fun r hr => D.regular_subset (hclock ht r hr)) times
      (fun k => ⟨hb₀.trans_le (htimes k).1, (htimes k).2⟩) htimesLim η hη x hη0
      (fun k => hηQ k ⟨(hb₀.trans_le (htimes k).1).le, le_rfl⟩)
      (show 0 ≤ n from Nat.cast_nonneg _) hq₀ hηbound
    intro c hc
    rcases hc.2.eq_or_lt with heq | hct
    · exact heq.symm ▸ (show Seed t from ⟨γ, hγ, hγ0, hγact⟩)
    · exact hbefore c ⟨hc.1, hct⟩
  have hall : Icc b₀ b₁ ⊆ P := by
    apply hPclosed.Icc_subset_of_forall_mem_nhdsWithin hP0
    intro b hb
    obtain ⟨α, hα, hα0, hαact⟩ := hb.1 b ⟨hb.2.1, le_rfl⟩
    have hcont := continuousOn_lRegularizedAction_end_time_of_carrier
      S hS.smoothMetric ⟨hS.scalarCont⟩ T (show (0 : ℝ) ≤ b₁ from hb₀.le.trans hband)
      α hα.contMDiffOn (fun r hr => D.regular_subset (hclock ⟨hband, le_rfl⟩ r hr))
    have hactNear : ∀ᶠ c in 𝓝 b, lRegularizedAction S T α 0 c < n * c := by
      have hc := (hcont b ⟨(hb₀.trans_le hb.2.1).le, hb.2.2.le⟩).continuousAt
        (Icc_mem_nhds (hb₀.trans_le hb.2.1) hb.2.2)
      exact (hc.sub (continuousAt_const.mul continuousAt_id)).eventually
        (Iio_mem_nhds (sub_neg.mpr hαact)) |>.mono fun _ hc => sub_neg.mp hc
    have hseedNear : {c | Seed c} ∈ 𝓝[>] b := by
      filter_upwards [hactNear.filter_mono nhdsWithin_le_nhds] with c hc
      exact ⟨α, hα, hα0, hc⟩
    obtain ⟨d, hbd, hd⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb.2.2).mp hseedNear
    filter_upwards [Ioo_mem_nhdsGT hbd] with c hc
    intro r hr
    rcases le_or_gt r b with hrb | hbr
    · exact hb.1 r ⟨hr.1, hrb⟩
    · exact hd ⟨hbr, hr.2.trans_lt hc.2⟩
  choose η hη hη0 hηQ hηmin hηbound using fun b hb => hbounded b hb (hall hb)
  let family : ℝ → ℝ → M := fun b => if hb : b ∈ Icc b₀ b₁ then η b hb else fun _ => x
  refine ⟨family, ?_⟩
  intro b hb
  have heq : family b = η b hb := dif_pos hb
  rw [heq]
  exact ⟨hη b hb, hη0 b hb, hηQ b hb, hηmin b hb, hηbound b hb,
    (hηbound b hb).trans_lt hq₀⟩

theorem exists_lRegularizedAction_lt_linear_at_carrier_endpoint_of_compact_action_sublevels
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ)
    {b₀ b₁ : ℝ} (hb₀ : 0 < b₀) (hband : b₀ < b₁)
    (hclock : ∀ t ∈ Icc 0 b₁, T - t ^ 2 ∈ D.carrier)
    (hreg : ∀ t ∈ Ico 0 b₁, T - t ^ 2 ∈ D.regular)
    (x : M) (Q : Set M) (hQ : IsCompact Q)
    (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 α₀) (hα₀start : α₀ 0 = x)
    (hα₀act : lRegularizedAction S T α₀ 0 b₀ < (Module.finrank ℝ E : ℝ) * b₀)
    (hconf : ∀ b ∈ Ico b₀ b₁, ∀ α : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 α → α 0 = x →
      lRegularizedAction S T α 0 b < (Module.finrank ℝ E : ℝ) * b →
      MapsTo α (Icc 0 b) Q) :
    ∃ b ∈ Ioo b₀ b₁, ∃ η : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 η ∧ η 0 = x ∧ MapsTo η (Icc 0 b) Q ∧
      (∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = x →
        lRegularizedAction S T η 0 b ≤ lRegularizedAction S T δ 0 b) ∧
      2 * b * lRegularizedAction S T η 0 b - 2 * (Module.finrank ℝ E : ℝ) * b ^ 2 ≤
        2 * b₀ * lRegularizedAction S T α₀ 0 b₀ - 2 * (Module.finrank ℝ E : ℝ) * b₀ ^ 2 ∧
      ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧ γ b₁ = η b ∧
        lRegularizedAction S T γ 0 b₁ < (Module.finrank ℝ E : ℝ) * b₁ := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨time, _, htime, hlim⟩ := exists_seq_strictMono_tendsto' hband
  have hslab (b : ℝ) (hb : b ∈ Ioo b₀ b₁) : Icc (T - b ^ 2) T ⊆ D.regular := by
    intro t ht
    have htT : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hroot : Real.sqrt (T - t) ≤ b :=
      (Real.sqrt_le_iff).mpr ⟨(hb₀.trans hb.1).le, by linarith [ht.1]⟩
    have hh := hreg (Real.sqrt (T - t)) ⟨Real.sqrt_nonneg _, hroot.trans_lt hb.2⟩
    simpa only [Real.sq_sqrt htT, sub_sub_cancel] using hh
  have hfamily (k : ℕ) := exists_free_endpoint_minimizers_of_compact_linear_action_sublevels
    S hS T hb₀ (hslab (time k) (htime k)) x Q hQ α₀ hα₀ hα₀start hα₀act
    (fun b hb => hconf b ⟨hb.1, hb.2.trans_lt (htime k).2⟩)
  choose η hη using hfamily
  have hdata (k : ℕ) := hη k (time k) ⟨(htime k).1.le, le_rfl⟩
  let κ := 2 * b₀ * lRegularizedAction S T α₀ 0 b₀ - 2 * (Module.finrank ℝ E : ℝ) * b₀ ^ 2
  have hκ : κ < 0 := by
    dsimp only [κ]
    nlinarith [mul_pos hb₀ (sub_pos.mpr hα₀act)]
  obtain ⟨k, γ, hγ, hγ0, hγend, hγact⟩ := exists_lRegularizedAction_lt_linear_of_tendsto_time
    S hS.smoothMetric ⟨hS.scalarCont⟩ T b₁ Q hQ hclock time
    (fun k => ⟨hb₀.trans (htime k).1, (htime k).2.le⟩) hlim
    (fun k => η k (time k)) (fun k => (hdata k).1) x (fun k => (hdata k).2.1)
    (fun k => (hdata k).2.2.1 ⟨(hb₀.trans (htime k).1).le, le_rfl⟩)
    (Nat.cast_nonneg (Module.finrank ℝ E)) hκ (fun k => (hdata k).2.2.2.2.1)
  exact ⟨time k, htime k, η k (time k), (hdata k).1, (hdata k).2.1, (hdata k).2.2.1,
    (hdata k).2.2.2.1, (hdata k).2.2.2.2.1, γ, hγ, hγ0, hγend, hγact⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
