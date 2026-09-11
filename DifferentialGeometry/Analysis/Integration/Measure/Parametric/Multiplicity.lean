import DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import DifferentialGeometry.Analysis.Integration.Measure.LocallyInjective

noncomputable section

open Set Function MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Integral.Measure

private theorem encard_fiber_eq_tsum_indicator
    {X Y : Type*} {f : X → Y} {K : Set X} {P : ℕ → Set X}
    (hPdisj : Pairwise (Disjoint on P)) (hPcover : (⋃ n, P n) = K)
    (hPinj : ∀ n, Set.InjOn f (P n)) (y : Y) :
    {x : X | x ∈ K ∧ f x = y}.encard.toENNReal =
      ∑' n : ℕ, (f '' P n).indicator 1 y := by
  classical
  have hPK : ∀ n, P n ⊆ K := by
    intro n x hx
    rw [← hPcover]
    exact Set.mem_iUnion.mpr ⟨n, hx⟩
  let Fib : Set X := {x : X | x ∈ K ∧ f x = y}
  let J : Set ℕ := {n : ℕ | y ∈ f '' P n}
  have hxpart : ∀ x : Fib, ∃ n, x.1 ∈ P n := by
    intro x
    have hx : x.1 ∈ ⋃ n, P n := hPcover.symm ▸ x.2.1
    exact Set.mem_iUnion.mp hx
  let idx : Fib → ℕ := fun x => Classical.choose (hxpart x)
  have hidx : ∀ x : Fib, x.1 ∈ P (idx x) := fun x =>
    Classical.choose_spec (hxpart x)
  let emb : Fib ↪ J :=
    { toFun := fun x => ⟨idx x, ⟨x.1, hidx x, x.2.2⟩⟩
      inj' := by
        intro x z hxz
        have hn : idx x = idx z := congrArg Subtype.val hxz
        apply Subtype.ext
        apply hPinj (idx x) (hidx x)
        · simpa only [hn] using hidx z
        · exact x.2.2.trans z.2.2.symm }
  have hsurj : Function.Surjective emb := by
    intro n
    obtain ⟨x, hxP, hxy⟩ := n.2
    let v : Fib := ⟨x, hPK n.1 hxP, hxy⟩
    refine ⟨v, Subtype.ext ?_⟩
    change idx v = n.1
    by_contra hne
    exact Set.disjoint_left.1 (hPdisj hne) (hidx v) hxP
  have hcard : Fib.encard = J.encard :=
    Set.encard_congr (Equiv.ofBijective emb ⟨emb.injective, hsurj⟩)
  calc
    Fib.encard.toENNReal = J.encard.toENNReal := congrArg ENat.toENNReal hcard
    _ = ∑' _ : J, (1 : ENNReal) := (ENNReal.tsum_set_one J).symm
    _ = ∑' n : ℕ, J.indicator 1 n :=
      tsum_subtype J (fun _ : ℕ => (1 : ENNReal))
    _ = ∑' n : ℕ, (f '' P n).indicator 1 y := by
      apply tsum_congr
      intro n
      simp only [J, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lintegral_encard_fiber_eq_lintegral_paramDensity
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U)
    (hloc : IsLocallyInjective (K.domRestrict f)) :
    ∫⁻ y, {x : E | x ∈ K ∧ f x = y}.encard.toENNReal
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) := by
  obtain ⟨P, hPmeas, hPdisj, hPcover, hPinj⟩ := hK.exists_partition_injOn hloc
  have hPK : ∀ n, P n ⊆ K := by
    intro n x hx
    rw [← hPcover]
    exact Set.mem_iUnion.mpr ⟨n, hx⟩
  have hQmeas : ∀ n, MeasurableSet (f '' P n) := fun n =>
    (hPmeas n).image_of_continuousOn_injOn
      (hf.continuousOn.mono ((hPK n).trans hKU)) (hPinj n)
  calc
    ∫⁻ y, {x : E | x ∈ K ∧ f x = y}.encard.toENNReal
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ y, ∑' n : ℕ, (f '' P n).indicator 1 y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          apply lintegral_congr
          exact encard_fiber_eq_tsum_indicator hPdisj hPcover hPinj
    _ = ∑' n : ℕ, ∫⁻ y, (f '' P n).indicator 1 y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          exact lintegral_tsum
            (fun n => (measurable_const.indicator (hQmeas n)).aemeasurable)
    _ = ∑' n : ℕ, riemannianVolumeMeasure (I := I) (M := M) g (f '' P n) := by
      apply tsum_congr
      intro n
      exact lintegral_indicator_one (hQmeas n)
    _ = ∑' n : ℕ, ∫⁻ x in P n, ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) := by
          apply tsum_congr
          intro n
          exact riemannianVolumeMeasure_image_eq (I := I) g hU (hPmeas n)
            ((hPK n).trans hKU) hf (hPinj n)
    _ = ∫⁻ x in ⋃ n, P n, ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) :=
          (lintegral_iUnion hPmeas hPdisj _).symm
    _ = ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) := by
          rw [hPcover]

theorem mul_riemannianVolumeMeasure_le_lintegral_paramDensity
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U)
    (hloc : IsLocallyInjective (K.domRestrict f))
    {S : Set M} (hS : MeasurableSet S) {m : ENat}
    (hcount : ∀ y ∈ S, m ≤ {x : E | x ∈ K ∧ f x = y}.encard) :
    m.toENNReal * riemannianVolumeMeasure (I := I) (M := M) g S ≤
      ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) := by
  calc
    m.toENNReal * riemannianVolumeMeasure (I := I) (M := M) g S =
        ∫⁻ _ in S, m.toENNReal
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      (setLIntegral_const S m.toENNReal).symm
    _ ≤ ∫⁻ y in S, {x : E | x ∈ K ∧ f x = y}.encard.toENNReal
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      setLIntegral_mono' hS (fun y hy => ENat.toENNReal_mono (hcount y hy))
    _ ≤ ∫⁻ y, {x : E | x ∈ K ∧ f x = y}.encard.toENNReal
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      setLIntegral_le_lintegral S _
    _ = ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x)
        ∂(modelHaar (E := E)) :=
      lintegral_encard_fiber_eq_lintegral_paramDensity (I := I) g hU hK hKU hf hloc

end DifferentialGeometry.Integral.Measure
