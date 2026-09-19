import Mathlib.Analysis.Analytic.Meromorphic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Sigma
noncomputable section
open Filter
open scoped Topology

theorem analytic_dslope_at_base {f : ℂ → ℂ} {p : ℂ} (h : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (dslope f p) p := by
  obtain ⟨P,hP⟩ := h
  exact ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩

/-- A nonzero numerator and a simple zero of the denominator give a genuine
meromorphic pole of order minus one, not merely a denominator zero. -/
theorem analytic_quotient_simple_pole {f g : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hf0 : f p ≠ 0) (hg0 : g p=0) (hgd : deriv g p ≠ 0) :
    ∃ hm : MeromorphicAt (fun z => f z/g z) p, hm.order=(-1 : ℤ) := by
  have hm : MeromorphicAt (fun z => f z/g z) p := hf.meromorphicAt.div hg.meromorphicAt
  refine ⟨hm,(hm.order_eq_int_iff (-1)).mpr ?_⟩
  refine ⟨fun z => f z/dslope g p z,
    hf.div (analytic_dslope_at_base hg) (by simpa only [dslope_same] using hgd),
    div_ne_zero hf0 (by simpa only [dslope_same] using hgd),?_⟩
  filter_upwards with z
  have he := sub_smul_dslope g p z
  simp only [smul_eq_mul,hg0,sub_zero] at he
  rw [←he]
  simp only [zpow_neg_one,smul_eq_mul,div_eq_mul_inv,mul_inv_rev]
  ring

def complexToddDenominator (z : ℂ) : ℂ := 1-Complex.exp (-z)

/-- Normalization by the genuine divided difference fills the removable value at zero. -/
def complexTodd (z : ℂ) : ℂ := (dslope complexToddDenominator 0 z)⁻¹
def complexAhat (z : ℂ) : ℂ := (dslope Complex.sinh 0 (z/2))⁻¹
def complexLgenus (z : ℂ) : ℂ := Complex.cosh z*(dslope Complex.sinh 0 z)⁻¹

theorem complex_todd_denominator_analytic (z : ℂ) :
    AnalyticAt ℂ complexToddDenominator z :=
  analyticAt_const.sub (analyticAt_id.neg.cexp)

theorem complex_todd_denominator_derivative (z : ℂ) :
    HasDerivAt complexToddDenominator (Complex.exp (-z)) z := by
  convert ((Complex.hasDerivAt_exp (-z)).comp z (hasDerivAt_id z).neg).const_sub 1 using 1
  simp [complexToddDenominator]

theorem complex_sinh_analytic (z : ℂ) : AnalyticAt ℂ Complex.sinh z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  exact Eventually.of_forall fun _ => Complex.differentiable_sinh.differentiableAt

theorem complex_cosh_analytic (z : ℂ) : AnalyticAt ℂ Complex.cosh z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  exact Eventually.of_forall fun _ => Complex.differentiable_cosh.differentiableAt

theorem complex_todd_zero : complexTodd 0=1 := by
  simp [complexTodd,dslope_same,(complex_todd_denominator_derivative 0).deriv]

theorem complex_ahat_zero : complexAhat 0=1 := by
  simp [complexAhat,dslope_same,Complex.deriv_sinh]

theorem complex_lgenus_zero : complexLgenus 0=1 := by
  simp [complexLgenus,dslope_same,Complex.deriv_sinh]

theorem complex_todd_quotient {z : ℂ} (hz : z ≠ 0) :
    complexTodd z=z/(1-Complex.exp (-z)) := by
  simp [complexTodd,dslope_of_ne _ hz,slope,complexToddDenominator,smul_eq_mul,div_eq_mul_inv]
  ring

theorem complex_ahat_quotient {z : ℂ} (hz : z ≠ 0) :
    complexAhat z=(z/2)/Complex.sinh (z/2) := by
  have h : z/2 ≠ 0 := div_ne_zero hz (by norm_num)
  unfold complexAhat
  rw [dslope_of_ne _ h]
  simp [slope,smul_eq_mul,div_eq_mul_inv]
  ring

theorem complex_lgenus_quotient {z : ℂ} (hz : z ≠ 0) :
    complexLgenus z=z*Complex.cosh z/Complex.sinh z := by
  simp [complexLgenus,dslope_of_ne _ hz,slope,smul_eq_mul,div_eq_mul_inv]
  ring

theorem complex_characteristic_analytic_zero :
    AnalyticAt ℂ complexTodd 0 ∧ AnalyticAt ℂ complexAhat 0 ∧
      AnalyticAt ℂ complexLgenus 0 := by
  have ht := analytic_dslope_at_base (complex_todd_denominator_analytic 0)
  have hs := analytic_dslope_at_base (complex_sinh_analytic 0)
  refine ⟨ht.inv ?_,?_,(complex_cosh_analytic 0).mul (hs.inv ?_)⟩
  · simp only [dslope_same,(complex_todd_denominator_derivative 0).deriv,neg_zero,Complex.exp_zero]
    exact one_ne_zero
  · have hi : AnalyticAt ℂ (fun z : ℂ => z/2) 0 :=
      analyticAt_id.div analyticAt_const (by norm_num)
    have ho : AnalyticAt ℂ (fun z => (dslope Complex.sinh 0 z)⁻¹) ((0 : ℂ)/2) := by
      simpa using hs.inv (by simp [dslope_same,Complex.deriv_sinh])
    exact ho.comp (f:=fun z : ℂ => z/2) hi
  · simp [dslope_same,Complex.deriv_sinh]

def HasSimpleComplexPole (f : ℂ → ℂ) (p : ℂ) : Prop :=
  ∃ hm : MeromorphicAt f p, hm.order=(-1 : ℤ)

theorem simple_complex_pole_congr {f g : ℂ → ℂ} {p : ℂ}
    (h : HasSimpleComplexPole f p) (he : f =ᶠ[𝓝[≠] p] g) :
    HasSimpleComplexPole g p := by
  obtain ⟨hm,ho⟩ := h
  have hn := hm.congr he
  refine ⟨hn,(hn.order_eq_int_iff (-1)).mpr ?_⟩
  obtain ⟨u,hu,hu0,heu⟩ := (hm.order_eq_int_iff (-1)).mp ho
  exact ⟨u,hu,hu0,he.symm.trans heu⟩

theorem complex_todd_denominator_zero_iff (z : ℂ) :
    complexToddDenominator z=0 ↔ ∃ n : ℤ, z=n*(2*Real.pi*Complex.I) := by
  unfold complexToddDenominator
  rw [sub_eq_zero,eq_comm,Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨-n,?_⟩
    push_cast
    linear_combination -hn
  · rintro ⟨n,rfl⟩
    refine ⟨-n,?_⟩
    push_cast
    ring

theorem complex_sinh_zero_iff (z : ℂ) :
    Complex.sinh z=0 ↔ ∃ n : ℤ, z=n*(Real.pi*Complex.I) := by
  change (Complex.exp z-Complex.exp (-z))/2=0 ↔ _
  rw [div_eq_zero_iff]
  norm_num only [OfNat.ofNat_ne_zero,or_false]
  rw [sub_eq_zero,Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,by linear_combination hn/2⟩
  · rintro ⟨n,rfl⟩
    exact ⟨n,by ring⟩

theorem complex_sinh_half_zero_iff (z : ℂ) :
    Complex.sinh (z/2)=0 ↔ ∃ n : ℤ, z=n*(2*Real.pi*Complex.I) := by
  rw [complex_sinh_zero_iff]
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,by linear_combination 2*hn⟩
  · rintro ⟨n,rfl⟩
    exact ⟨n,by ring⟩

theorem complex_cosh_ne_zero_at_sinh_zero {z : ℂ} (h : Complex.sinh z=0) :
    Complex.cosh z ≠ 0 := by
  intro hc
  have he := Complex.cosh_sq_sub_sinh_sq z
  simp [h,hc] at he

theorem complex_todd_simple_pole {p : ℂ} (hp : p ≠ 0)
    (hd : complexToddDenominator p=0) : HasSimpleComplexPole complexTodd p := by
  have h := analytic_quotient_simple_pole (f:=fun z : ℂ => z)
    analyticAt_id (complex_todd_denominator_analytic p) hp hd
    (by rw [(complex_todd_denominator_derivative p).deriv]; exact Complex.exp_ne_zero _)
  apply simple_complex_pole_congr h
  filter_upwards [(eventually_ne_nhds hp).filter_mono nhdsWithin_le_nhds] with z hz
  exact (complex_todd_quotient hz).symm

theorem complex_ahat_simple_pole {p : ℂ} (hp : p ≠ 0)
    (hd : Complex.sinh (p/2)=0) : HasSimpleComplexPole complexAhat p := by
  have hi : AnalyticAt ℂ (fun z : ℂ => z/2) p :=
    analyticAt_id.div analyticAt_const (by norm_num)
  have hg := (complex_sinh_analytic (p/2)).comp (f:=fun z : ℂ => z/2) hi
  have hd' : HasDerivAt (fun z : ℂ => Complex.sinh (z/2)) (Complex.cosh (p/2)/2) p := by
    convert (Complex.hasDerivAt_sinh (p/2)).comp p ((hasDerivAt_id p).div_const 2) using 1
    ring
  have h := analytic_quotient_simple_pole hi hg (div_ne_zero hp (by norm_num)) hd
    (by change deriv (fun z : ℂ => Complex.sinh (z/2)) p ≠ 0
        rw [hd'.deriv]
        exact div_ne_zero (complex_cosh_ne_zero_at_sinh_zero hd) (by norm_num))
  apply simple_complex_pole_congr h
  filter_upwards [(eventually_ne_nhds hp).filter_mono nhdsWithin_le_nhds] with z hz
  exact (complex_ahat_quotient hz).symm

theorem complex_lgenus_simple_pole {p : ℂ} (hp : p ≠ 0)
    (hd : Complex.sinh p=0) : HasSimpleComplexPole complexLgenus p := by
  have h := analytic_quotient_simple_pole (analyticAt_id.mul (complex_cosh_analytic p))
    (complex_sinh_analytic p) (mul_ne_zero hp (complex_cosh_ne_zero_at_sinh_zero hd)) hd
    (by rw [Complex.deriv_sinh]; exact complex_cosh_ne_zero_at_sinh_zero hd)
  apply simple_complex_pole_congr h
  filter_upwards [(eventually_ne_nhds hp).filter_mono nhdsWithin_le_nhds] with z hz
  exact (complex_lgenus_quotient hz).symm

theorem simple_complex_pole_not_analytic {f : ℂ → ℂ} {p : ℂ}
    (h : HasSimpleComplexPole f p) : ¬ AnalyticAt ℂ f p := by
  intro ha
  obtain ⟨hm,ho⟩ := h
  have he : hm.order=ha.order.map (fun n : ℕ => (n : ℤ)) := ha.meromorphicAt_order
  rw [ho] at he
  rcases eq_or_ne ha.order ⊤ with ht | ht
  · rw [ht,WithTop.map_top] at he
    exact WithTop.coe_ne_top he
  · obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [←hn,WithTop.map_coe] at he
    have he' : (-1 : ℤ)=(n : ℤ) := WithTop.coe_inj.mp he
    omega

theorem complex_todd_analytic_of_regular {p : ℂ} (hp : p ≠ 0)
    (hd : complexToddDenominator p ≠ 0) : AnalyticAt ℂ complexTodd p := by
  apply (analyticAt_id.div (complex_todd_denominator_analytic p) hd).congr
  filter_upwards [eventually_ne_nhds hp] with z hz
  exact (complex_todd_quotient hz).symm

theorem complex_ahat_analytic_of_regular {p : ℂ} (hp : p ≠ 0)
    (hd : Complex.sinh (p/2) ≠ 0) : AnalyticAt ℂ complexAhat p := by
  have hi : AnalyticAt ℂ (fun z : ℂ => z/2) p :=
    analyticAt_id.div analyticAt_const (by norm_num)
  apply (hi.div ((complex_sinh_analytic (p/2)).comp (f:=fun z : ℂ => z/2) hi) hd).congr
  filter_upwards [eventually_ne_nhds hp] with z hz
  exact (complex_ahat_quotient hz).symm

theorem complex_lgenus_analytic_of_regular {p : ℂ} (hp : p ≠ 0)
    (hd : Complex.sinh p ≠ 0) : AnalyticAt ℂ complexLgenus p := by
  apply ((analyticAt_id.mul (complex_cosh_analytic p)).div (complex_sinh_analytic p) hd).congr
  filter_upwards [eventually_ne_nhds hp] with z hz
  exact (complex_lgenus_quotient hz).symm

theorem complex_todd_poles_iff (p : ℂ) :
    HasSimpleComplexPole complexTodd p ↔ p ≠ 0 ∧ ∃ n : ℤ, p=n*(2*Real.pi*Complex.I) := by
  constructor
  · intro h
    have hp : p ≠ 0 := by
      rintro rfl
      exact simple_complex_pole_not_analytic h complex_characteristic_analytic_zero.1
    refine ⟨hp,(complex_todd_denominator_zero_iff p).mp ?_⟩
    by_contra hd
    exact simple_complex_pole_not_analytic h (complex_todd_analytic_of_regular hp hd)
  · rintro ⟨hp,hn⟩
    exact complex_todd_simple_pole hp ((complex_todd_denominator_zero_iff p).mpr hn)

theorem complex_ahat_poles_iff (p : ℂ) :
    HasSimpleComplexPole complexAhat p ↔ p ≠ 0 ∧ ∃ n : ℤ, p=n*(2*Real.pi*Complex.I) := by
  constructor
  · intro h
    have hp : p ≠ 0 := by
      rintro rfl
      exact simple_complex_pole_not_analytic h complex_characteristic_analytic_zero.2.1
    refine ⟨hp,(complex_sinh_half_zero_iff p).mp ?_⟩
    by_contra hd
    exact simple_complex_pole_not_analytic h (complex_ahat_analytic_of_regular hp hd)
  · rintro ⟨hp,hn⟩
    exact complex_ahat_simple_pole hp ((complex_sinh_half_zero_iff p).mpr hn)

theorem complex_lgenus_poles_iff (p : ℂ) :
    HasSimpleComplexPole complexLgenus p ↔ p ≠ 0 ∧ ∃ n : ℤ, p=n*(Real.pi*Complex.I) := by
  constructor
  · intro h
    have hp : p ≠ 0 := by
      rintro rfl
      exact simple_complex_pole_not_analytic h complex_characteristic_analytic_zero.2.2
    refine ⟨hp,(complex_sinh_zero_iff p).mp ?_⟩
    by_contra hd
    exact simple_complex_pole_not_analytic h (complex_lgenus_analytic_of_regular hp hd)
  · rintro ⟨hp,hn⟩
    exact complex_lgenus_simple_pole hp ((complex_sinh_zero_iff p).mpr hn)

theorem integer_imaginary_lattice_norm (r : ℝ) (hr : 0<r) (n : ℤ) :
    ‖(n : ℂ)*((r : ℂ)*Complex.I)‖=|(n : ℝ)| * r := by
  simp [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]

theorem integer_imaginary_lattice_nearest (r : ℝ) (hr : 0<r) (p : ℂ)
    (hp : p ≠ 0) (hl : ∃ n : ℤ, p=n*((r : ℂ)*Complex.I)) :
    r ≤ ‖p‖ ∧ (‖p‖=r ↔ p=(r : ℂ)*Complex.I ∨ p= -((r : ℂ)*Complex.I)) := by
  obtain ⟨n,rfl⟩ := hl
  have hn : n ≠ 0 := by intro hn; simp [hn] at hp
  have ha : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  rw [integer_imaginary_lattice_norm r hr n]
  refine ⟨by nlinarith,?_⟩
  constructor
  · intro he
    have habs : |(n : ℝ)|=1 := by nlinarith
    rcases le_total (0 : ℝ) n with hs | hs
    · rw [abs_of_nonneg hs] at habs
      have hn1 : n=1 := by exact_mod_cast habs
      simp [hn1]
    · rw [abs_of_nonpos hs] at habs
      have hn1 : n= -1 := by exact_mod_cast (show (n : ℝ)= -1 by linarith)
      simp [hn1]
  · intro he
    rcases he with he | he
    · have hn1 : (n : ℂ)=1 := (mul_right_cancel₀ (mul_ne_zero (show (r : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hr)
        Complex.I_ne_zero)) (by simpa using he)
      have hn1' : n=1 := by exact_mod_cast hn1
      simp [hn1']
    · have hn1 : (n : ℂ)= -1 := (mul_right_cancel₀ (mul_ne_zero (show (r : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hr)
        Complex.I_ne_zero)) (by simpa using he)
      have hn1' : n= -1 := by exact_mod_cast hn1
      simp [hn1']

theorem complex_todd_ahat_nearest_poles (p : ℂ)
    (h : HasSimpleComplexPole complexTodd p ∨ HasSimpleComplexPole complexAhat p) :
    2*Real.pi ≤ ‖p‖ ∧ (‖p‖=2*Real.pi ↔
      p=2*Real.pi*Complex.I ∨ p= -(2*Real.pi*Complex.I)) := by
  have hp : p ≠ 0 ∧ ∃ n : ℤ, p=n*(2*Real.pi*Complex.I) := by
    rcases h with ht | ha
    · exact (complex_todd_poles_iff p).mp ht
    · exact (complex_ahat_poles_iff p).mp ha
  simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
    integer_imaginary_lattice_nearest (2*Real.pi) (by positivity) p hp.1
      (by simpa using hp.2)

theorem complex_lgenus_nearest_poles (p : ℂ) (h : HasSimpleComplexPole complexLgenus p) :
    Real.pi ≤ ‖p‖ ∧ (‖p‖=Real.pi ↔ p=Real.pi*Complex.I ∨ p= -(Real.pi*Complex.I)) := by
  obtain ⟨hp,hl⟩ := (complex_lgenus_poles_iff p).mp h
  exact integer_imaginary_lattice_nearest Real.pi Real.pi_pos p hp hl

theorem complex_characteristic_boundary_poles :
    HasSimpleComplexPole complexTodd (2*Real.pi*Complex.I) ∧
    HasSimpleComplexPole complexTodd (-(2*Real.pi*Complex.I)) ∧
    HasSimpleComplexPole complexAhat (2*Real.pi*Complex.I) ∧
    HasSimpleComplexPole complexAhat (-(2*Real.pi*Complex.I)) ∧
    HasSimpleComplexPole complexLgenus (Real.pi*Complex.I) ∧
    HasSimpleComplexPole complexLgenus (-(Real.pi*Complex.I)) := by
  have hp : (Real.pi : ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have hp2 : (2 : ℂ)*Real.pi*Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  simp only [complex_todd_poles_iff,complex_ahat_poles_iff,complex_lgenus_poles_iff]
  have hpos (z : ℂ) : ∃ n : ℤ, z=n*z := ⟨1,by simp⟩
  have hneg (z : ℂ) : ∃ n : ℤ, -z=n*z := ⟨-1,by simp⟩
  exact ⟨⟨hp2,hpos _⟩,⟨neg_ne_zero.mpr hp2,hneg _⟩,
    ⟨hp2,hpos _⟩,⟨neg_ne_zero.mpr hp2,hneg _⟩,
    ⟨hp,hpos _⟩,⟨neg_ne_zero.mpr hp,hneg _⟩⟩

end
end Sigma
