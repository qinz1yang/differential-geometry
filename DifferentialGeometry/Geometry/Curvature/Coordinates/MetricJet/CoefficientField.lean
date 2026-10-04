import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.Curvature
import DifferentialGeometry.Analysis.Calculus.TimeJet.Evolution
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Tensor.Coordinates.ModelBasis

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ContDiff
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)
open DifferentialGeometry.CheegerGromovCompactness (MapCPConvergenceOn mapDerivNorm
  mapDerivNorm_nonneg tendstoUniformlyOn_of_cPConvergence)
namespace DifferentialGeometry.Analysis

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
def coefficientGramCLM :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
  ContinuousLinearMap.pi fun l => ContinuousLinearMap.pi fun m =>
    (ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E m)).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (chartModelBasis E l))

def coefficientGram (b : E → E →L[ℝ] E →L[ℝ] ℝ) :
    E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun w => coefficientGramCLM E (b w)

theorem coefficientGram_apply (b : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E)
    (l m : Fin (Module.finrank ℝ E)) :
    coefficientGram b w l m = b w (chartModelBasis E l) (chartModelBasis E m) :=
  rfl

def jetRm04 (p : MatJet E (Module.finrank ℝ E)) (X Y Z W : E) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, (chartModelBasis E).repr X i * (chartModelBasis E).repr Y j *
    (chartModelBasis E).repr Z k * (chartModelBasis E).repr W l *
      ∑ l', p.1 l l' * jetRiemann (chartModelBasis E) p k i j l'

def coefficientRm04 (b : E → E →L[ℝ] E →L[ℝ] ℝ) (w X Y Z W : E) : ℝ :=
  jetRm04 (jet2 (coefficientGram b) w) X Y Z W

theorem coefficientRm04_eq_sum (b : E → E →L[ℝ] E →L[ℝ] ℝ) (w X Y Z W : E) :
    coefficientRm04 b w X Y Z W =
      ∑ i, ∑ j, ∑ k, ∑ l, (chartModelBasis E).repr X i * (chartModelBasis E).repr Y j *
        (chartModelBasis E).repr Z k * (chartModelBasis E).repr W l *
          ∑ l', coefficientGram b w l l' *
            jetRiemann (chartModelBasis E) (jet2 (coefficientGram b) w) k i j l' :=
  rfl

theorem jetRm04_eq_sectional_order (p : MatJet E (Module.finrank ℝ E)) (v u : E) :
    jetRm04 p v u u v =
      ∑ i, ∑ j, ∑ k, ∑ l, (chartModelBasis E).repr v l * (chartModelBasis E).repr u i *
        (chartModelBasis E).repr v j * (chartModelBasis E).repr u k *
          ∑ m, p.1 l m * jetRiemann (chartModelBasis E) p i j k m := by
  unfold jetRm04
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

theorem contDiffOn_coefficientGram {n : ℕ∞ω} {b : E → E →L[ℝ] E →L[ℝ] ℝ} {s : Set E}
    (hb : ContDiffOn ℝ n b s) : ContDiffOn ℝ n (coefficientGram b) s :=
  (coefficientGramCLM E).contDiff.comp_contDiffOn hb

theorem contDiffAt_coefficientGram {n : ℕ∞ω} {b : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}
    (hb : ContDiffAt ℝ n b w) : ContDiffAt ℝ n (coefficientGram b) w :=
  (coefficientGramCLM E).contDiff.comp_contDiffAt w hb

private theorem det_coefficientGram_ne_zero {b : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}
    (hpos : ∀ v : E, v ≠ 0 → 0 < b w v v) :
    (Matrix.of (coefficientGram b w)).det ≠ 0 := by
  intro hdet0
  obtain ⟨c, hc0, hcv⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := Matrix.of (coefficientGram b w))).2 hdet0
  set v : E := ∑ i, c i • chartModelBasis E i with hv
  have hrow0 : ∀ i, (b w (chartModelBasis E i)) v = 0 := by
    intro i
    have h1 : (b w (chartModelBasis E i)) v =
        ∑ j, Matrix.of (coefficientGram b w) i j * c j := by
      rw [hv, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      simp only [coefficientGram_apply, Matrix.of_apply]
    have h2 : (∑ j, Matrix.of (coefficientGram b w) i j * c j) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hcv i
    rw [h1, h2]
  have hinner : b w v v = 0 := by
    have hout : (b w) v = ∑ i, c i • ((b w) (chartModelBasis E i)) := by
      rw [hv, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    calc b w v v = (∑ i, c i • ((b w) (chartModelBasis E i))) v := by rw [hout]
      _ = ∑ i, c i • ((b w (chartModelBasis E i)) v) := by
          rw [_root_.sum_apply]
          exact Finset.sum_congr rfl fun i _ => by rw [_root_.smul_apply]
      _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hrow0 i, smul_zero]
  have hvne : v ≠ 0 := by
    intro hv0
    apply hc0
    have hz : ∑ i, c i • chartModelBasis E i = 0 := hv.symm.trans hv0
    have hall := Fintype.linearIndependent_iff.1 (chartModelBasis E).linearIndependent c hz
    funext i
    exact hall i
  exact absurd hinner (ne_of_gt (hpos v hvne))

private theorem contDiffAt_jetRm04 {p₀ : MatJet E (Module.finrank ℝ E)}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (X Y Z W : E) :
    ContDiffAt ℝ ∞ (fun p : MatJet E (Module.finrank ℝ E) => jetRm04 p X Y Z W) p₀ := by
  unfold jetRm04
  refine ContDiffAt.sum (fun i _ => ?_)
  refine ContDiffAt.sum (fun j _ => ?_)
  refine ContDiffAt.sum (fun k _ => ?_)
  refine ContDiffAt.sum (fun l _ => ?_)
  refine contDiffAt_const.mul (ContDiffAt.sum (fun l' _ => ?_))
  exact (contDiff_jetVal l l').contDiffAt.mul (contDiffAt_jetRiemann _ hp₀ k i j l')

omit [FiniteDimensional ℝ E] in
theorem jet2_congr_of_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {w : E} (h : f =ᶠ[𝓝 w] g) : jet2 f w = jet2 g w := by
  have h1 : (fun y => fderiv ℝ f y) =ᶠ[𝓝 w] (fun y => fderiv ℝ g y) :=
    h.eventuallyEq_nhds.mono fun y hy => hy.fderiv_eq
  exact Prod.ext h.eq_of_nhds (Prod.ext h.fderiv_eq h1.fderiv_eq)

end

section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem mapCPConvergenceOn_comp_clm {U D : Set E} (hU : IsOpen U) (hDU : D ⊆ U) {p : ℕ}
    {f : ℕ → E → F} {f₀ : E → F} (hf : ∀ i, ContDiffOn ℝ p (f i) U)
    (hf₀ : ContDiffOn ℝ p f₀ U) (L : F →L[ℝ] G) (h : MapCPConvergenceOn D p f f₀) :
    MapCPConvergenceOn D p (fun i y => L (f i y)) (fun y => L (f₀ y)) := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h (ε / (‖L‖ + 1)) (by positivity)
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hd : ContDiffAt ℝ p (fun y => f k y - f₀ y) x :=
    ((hf k).sub hf₀).contDiffAt (hU.mem_nhds (hDU hx))
  have hb : ‖iteratedFDeriv ℝ r (fun y => f k y - f₀ y) x‖ ≤ ε / (‖L‖ + 1) :=
    hk0 k hk r hr x hx
  have heq : (fun y => L (f k y) - L (f₀ y)) = L ∘ (fun y => f k y - f₀ y) := by
    funext y
    simp only [Function.comp_apply, map_sub]
  have hcomp : iteratedFDeriv ℝ r (fun y => L (f k y) - L (f₀ y)) x =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ r (fun y => f k y - f₀ y) x) := by
    rw [heq]
    exact L.iteratedFDeriv_comp_left hd (by exact_mod_cast hr)
  have hbound : ‖iteratedFDeriv ℝ r (fun y => L (f k y) - L (f₀ y)) x‖ ≤ ε := by
    rw [hcomp]
    have hL := norm_nonneg L
    calc ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ r (fun y => f k y - f₀ y) x)‖
        ≤ ‖L‖ * ‖iteratedFDeriv ℝ r (fun y => f k y - f₀ y) x‖ :=
          L.norm_compContinuousMultilinearMap_le _
      _ ≤ ‖L‖ * (ε / (‖L‖ + 1)) := mul_le_mul_of_nonneg_left hb hL
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  exact hbound

theorem tendsto_jet2_of_mapCPConvergenceOn {U D : Set E} (hU : IsOpen U) (hDU : D ⊆ U)
    {f : ℕ → E → F} {f₀ : E → F} (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hf₀ : ContDiffOn ℝ 2 f₀ U) (hconv : MapCPConvergenceOn D 2 f f₀) {w : E} (hw : w ∈ D) :
    Tendsto (fun i => jet2 (f i) w) atTop (𝓝 (jet2 f₀ w)) := by
  have hwU : U ∈ 𝓝 w := hU.mem_nhds (hDU hw)
  have hdU (i : ℕ) (y : E) (hy : y ∈ U) : DifferentiableAt ℝ (f i) y :=
    ((hf i).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hdU₀ (y : E) (hy : y ∈ U) : DifferentiableAt ℝ f₀ y :=
    (hf₀.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hdd (i : ℕ) : DifferentiableAt ℝ (fun y => fderiv ℝ (f i) y) w :=
    (((hf i).contDiffAt hwU).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdd₀ : DifferentiableAt ℝ (fun y => fderiv ℝ f₀ y) w :=
    ((hf₀.contDiffAt hwU).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hmd (r : ℕ) (hr : r ≤ 2) :
      Tendsto (fun i => mapDerivNorm r (f i) f₀ w) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k0, hk0⟩ := hconv (ε / 2) (by positivity)
    refine ⟨k0, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mapDerivNorm_nonneg r (f k) f₀ w)]
    exact (hk0 k hk r hr w hw).trans_lt (by linarith)
  have h0 : Tendsto (fun i => f i w) atTop (𝓝 (f₀ w)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ((hmd 0 (Nat.zero_le 2)).congr fun i => ?_)
    exact norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fun y => f i y - f₀ y) (x := w)
  have h1 : Tendsto (fun i => fderiv ℝ (f i) w) atTop (𝓝 (fderiv ℝ f₀ w)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ((hmd 1 (by norm_num)).congr fun i => ?_)
    have hn := norm_iteratedFDeriv_one (𝕜 := ℝ) (fun y => f i y - f₀ y) (x := w)
    rw [fderiv_fun_sub (hdU i w (hDU hw)) (hdU₀ w (hDU hw))] at hn
    exact hn
  have h2 : Tendsto (fun i => fderiv ℝ (fun y => fderiv ℝ (f i) y) w) atTop
      (𝓝 (fderiv ℝ (fun y => fderiv ℝ f₀ y) w)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ((hmd 2 le_rfl).congr fun i => ?_)
    have hev : (fderiv ℝ (fun y => f i y - f₀ y)) =ᶠ[𝓝 w]
        (fun y => fderiv ℝ (f i) y - fderiv ℝ f₀ y) := by
      filter_upwards [hwU] with y hy
      exact fderiv_fun_sub (hdU i y hy) (hdU₀ y hy)
    have hsec : fderiv ℝ (fderiv ℝ (fun y => f i y - f₀ y)) w =
        fderiv ℝ (fun y => fderiv ℝ (f i) y) w - fderiv ℝ (fun y => fderiv ℝ f₀ y) w :=
      hev.fderiv_eq.trans (fderiv_fun_sub (hdd i) hdd₀)
    have hn := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1) (f := fun y => f i y - f₀ y)
      (x := w)
    rw [norm_iteratedFDeriv_one, hsec] at hn
    exact hn.symm
  exact h0.prodMk_nhds (h1.prodMk_nhds h2)

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem tendsto_jet2_coefficientGram_of_mapCPConvergenceOn {U D : Set E} (hU : IsOpen U)
    (hDU : D ⊆ U) {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ i, ContDiffOn ℝ 2 (B i) U) (hb : ContDiffOn ℝ 2 b U)
    (hconv : MapCPConvergenceOn D 2 B b) {w : E} (hw : w ∈ D) :
    Tendsto (fun i => jet2 (coefficientGram (B i)) w) atTop
      (𝓝 (jet2 (coefficientGram b) w)) :=
  tendsto_jet2_of_mapCPConvergenceOn hU hDU (fun i => contDiffOn_coefficientGram (hB i))
    (contDiffOn_coefficientGram hb)
    (mapCPConvergenceOn_comp_clm hU hDU hB hb (coefficientGramCLM E) hconv) hw

theorem tendsto_coefficientRm04_of_mapCPConvergenceOn {U D : Set E} (hU : IsOpen U)
    (hDU : D ⊆ U) {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ i, ContDiffOn ℝ 2 (B i) U) (hb : ContDiffOn ℝ 2 b U)
    (hconv : MapCPConvergenceOn D 2 B b) {w : E} (hw : w ∈ D)
    (hpos : ∀ v : E, v ≠ 0 → 0 < b w v v) (X Y Z W : E) :
    Tendsto (fun i => coefficientRm04 (B i) w X Y Z W) atTop
      (𝓝 (coefficientRm04 b w X Y Z W)) := by
  have hdet : (Matrix.of (jet2 (coefficientGram b) w).1).det ≠ 0 :=
    det_coefficientGram_ne_zero hpos
  exact ((contDiffAt_jetRm04 hdet X Y Z W).continuousAt.tendsto).comp
    (tendsto_jet2_coefficientGram_of_mapCPConvergenceOn hU hDU hB hb hconv hw)

theorem nonneg_coefficientRm04_of_eventual_sectional_lower_bound {U D : Set E}
    (hU : IsOpen U) (hDU : D ⊆ U) {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ}
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} (hB : ∀ i, ContDiffOn ℝ 2 (B i) U)
    (hb : ContDiffOn ℝ 2 b U) (hconv : MapCPConvergenceOn D 2 B b)
    (hpos : ∀ w ∈ D, ∀ v : E, v ≠ 0 → 0 < b w v v) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hlow : ∀ᶠ i in atTop, ∀ w ∈ D, ∀ v u : E,
      -ε i * (B i w v v * B i w u u - (B i w v u) ^ 2) ≤ coefficientRm04 (B i) w v u u v) :
    ∀ w ∈ D, ∀ v u : E, 0 ≤ coefficientRm04 b w v u u v := by
  intro w hw v u
  have hR := tendsto_coefficientRm04_of_mapCPConvergenceOn hU hDU hB hb hconv hw
    (hpos w hw) v u u v
  have hval : Tendsto (fun i => B i w) atTop (𝓝 (b w)) :=
    (tendstoUniformlyOn_of_cPConvergence (hconv.mono_order (Nat.zero_le 2))).tendsto_at hw
  have hev (x y : E) : Continuous (fun C : E →L[ℝ] E →L[ℝ] ℝ => C x y) := by
    fun_prop
  have hvv : Tendsto (fun i => B i w v v) atTop (𝓝 (b w v v)) :=
    ((hev v v).tendsto (b w)).comp hval
  have huu : Tendsto (fun i => B i w u u) atTop (𝓝 (b w u u)) :=
    ((hev u u).tendsto (b w)).comp hval
  have hvu : Tendsto (fun i => B i w v u) atTop (𝓝 (b w v u)) :=
    ((hev v u).tendsto (b w)).comp hval
  have hden : Tendsto (fun i => B i w v v * B i w u u - (B i w v u) ^ 2) atTop
      (𝓝 (b w v v * b w u u - (b w v u) ^ 2)) :=
    (hvv.mul huu).sub (hvu.pow 2)
  have hlhs : Tendsto (fun i => -ε i * (B i w v v * B i w u u - (B i w v u) ^ 2)) atTop
      (𝓝 0) := by
    have h := hε.neg.mul hden
    rw [neg_zero, zero_mul] at h
    exact h
  exact le_of_tendsto_of_tendsto hlhs hR (hlow.mono fun i hi => hi w hw v u)

end

end DifferentialGeometry.Analysis
