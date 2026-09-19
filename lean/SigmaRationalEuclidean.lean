import SigmaRealArithmetic
import Mathlib.Data.Rat.Floor

namespace Sigma
noncomputable section

/-- Ordinary finite simple continued-fraction evaluation. -/
def finiteCFValue : List ℕ → ℚ
  | [] => 0
  | a::l => a+(finiteCFValue l)⁻¹

/-- Positive internal digits, with the canonical terminal digit at least two. -/
inductive CanonicalCFTail : List ℕ → Prop
  | last (a : ℕ) (ha : 2 ≤ a) : CanonicalCFTail [a]
  | cons (a : ℕ) (l : List ℕ) (ha : 1 ≤ a) (hl : CanonicalCFTail l) :
      CanonicalCFTail (a::l)

/-- The first digit is nonnegative; a singleton must be positive. -/
inductive CanonicalPositiveCF : List ℕ → Prop
  | single (a : ℕ) (ha : 1 ≤ a) : CanonicalPositiveCF [a]
  | cons (a : ℕ) (l : List ℕ) (hl : CanonicalCFTail l) : CanonicalPositiveCF (a::l)

theorem canonical_cf_tail_gt_one {l : List ℕ} (h : CanonicalCFTail l) :
    1 < finiteCFValue l := by
  induction h with
  | last a ha => simp only [finiteCFValue, inv_zero, add_zero]; exact_mod_cast ha
  | cons a l ha hl ih =>
    simp only [finiteCFValue]
    have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
    have hi : 0 < (finiteCFValue l)⁻¹ := inv_pos.mpr (lt_trans zero_lt_one ih)
    linarith

theorem canonical_cf_tail_positive {l : List ℕ} (h : CanonicalCFTail l) :
    0 < finiteCFValue l := lt_trans zero_lt_one (canonical_cf_tail_gt_one h)

theorem canonical_cf_positive {l : List ℕ} (h : CanonicalPositiveCF l) :
    0 < finiteCFValue l := by
  cases h with
  | single a ha => simp only [finiteCFValue, inv_zero, add_zero]; exact_mod_cast ha
  | cons a l hl =>
    simp only [finiteCFValue]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg a) (inv_pos.mpr (canonical_cf_tail_positive hl))

theorem canonical_cf_tail_is_canonical {l : List ℕ} (h : CanonicalCFTail l) :
    CanonicalPositiveCF l := by
  cases h with
  | last a ha => exact .single a (by omega)
  | cons a l ha hl => exact .cons a l hl

theorem canonical_cf_gt_one_tail {l : List ℕ} (h : CanonicalPositiveCF l)
    (hv : 1 < finiteCFValue l) : CanonicalCFTail l := by
  cases h with
  | single a ha =>
    simp only [finiteCFValue, inv_zero, add_zero] at hv
    exact .last a (by exact_mod_cast hv)
  | cons a l hl =>
    refine .cons a l ?_ hl
    by_contra ha
    have ha0 : a=0 := by omega
    have hi : (finiteCFValue l)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (canonical_cf_tail_gt_one hl)
    simp only [finiteCFValue, ha0, Nat.cast_zero, zero_add] at hv
    linarith

theorem finite_cf_division_identity (a b : ℕ) (hb : 0 < b)
    (hr : 0 < a%b) :
    (a : ℚ)/b=(a/b : ℕ)+((b : ℚ)/((a%b : ℕ) : ℚ))⁻¹ := by
  have hb0 : (b : ℚ) ≠ 0 := by positivity
  have hr0 : ((a%b : ℕ) : ℚ) ≠ 0 := by positivity
  have he := Nat.mod_add_div a b
  have he' : ((a%b : ℕ) : ℚ)+(b : ℚ)*(a/b : ℕ)=a := by exact_mod_cast he
  rw [inv_div]
  field_simp
  nlinarith

theorem canonical_cf_exists_fraction (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ l, CanonicalPositiveCF l ∧ finiteCFValue l=(a : ℚ)/b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases hr : a%b=0
    · have he : b*(a/b)=a := by simpa [hr] using Nat.mod_add_div a b
      have hq : 1 ≤ a/b := by nlinarith
      refine ⟨[a/b], .single _ hq, ?_⟩
      simp only [finiteCFValue, inv_zero, add_zero]
      apply (eq_div_iff (by positivity : (b : ℚ) ≠ 0)).mpr
      exact_mod_cast (mul_comm (a/b) b).trans he
    · have hrp : 0 < a%b := Nat.pos_of_ne_zero hr
      obtain ⟨l,hl,hv⟩ := ih (a%b) (Nat.mod_lt a hb) b hb hrp
      have hgt : 1 < finiteCFValue l := by
        rw [hv]
        apply (one_lt_div (by positivity : (0 : ℚ)<(a%b : ℕ))).mpr
        exact_mod_cast Nat.mod_lt a hb
      refine ⟨(a/b)::l, .cons _ _ (canonical_cf_gt_one_tail hl hgt), ?_⟩
      rw [finiteCFValue, hv]
      exact (finite_cf_division_identity a b hb hrp).symm

theorem canonical_cf_head_floor {a : ℕ} {l : List ℕ}
    (h : CanonicalPositiveCF (a::l)) : ⌊finiteCFValue (a::l)⌋=(a : ℤ) := by
  apply Int.floor_eq_iff.mpr
  cases h with
  | single a ha => simp [finiteCFValue]
  | cons a l hl =>
    have hp := inv_pos.mpr (canonical_cf_tail_positive hl)
    have hu := inv_lt_one_of_one_lt₀ (canonical_cf_tail_gt_one hl)
    simp only [finiteCFValue, Int.cast_natCast]
    constructor <;> linarith

theorem canonical_cf_injective {l m : List ℕ} (hl : CanonicalPositiveCF l)
    (hm : CanonicalPositiveCF m) (hv : finiteCFValue l=finiteCFValue m) : l=m := by
  induction l generalizing m with
  | nil => cases hl
  | cons a l ih =>
    cases m with
    | nil => cases hm
    | cons b m =>
      have hab : a=b := by
        have he := congrArg Int.floor hv
        rw [canonical_cf_head_floor hl, canonical_cf_head_floor hm] at he
        exact_mod_cast he
      subst b
      have ht : finiteCFValue l=finiteCFValue m := by
        simp only [finiteCFValue] at hv
        exact inv_injective (add_left_cancel hv)
      congr 1
      cases hl with
      | single a ha =>
        cases hm with
        | single a hb => rfl
        | cons a m hm =>
          have hp := canonical_cf_tail_positive hm
          simp only [finiteCFValue] at ht
          linarith
      | cons a l hl =>
        cases hm with
        | single a ha =>
          have hp := canonical_cf_tail_positive hl
          simp only [finiteCFValue] at ht
          linarith
        | cons a m hm =>
          exact ih (canonical_cf_tail_is_canonical hl) (canonical_cf_tail_is_canonical hm) ht

theorem canonical_cf_exists_unique (q : ℚ) (hq : 0 < q) :
    ∃! l, CanonicalPositiveCF l ∧ finiteCFValue l=q := by
  have hn : 0 < q.num := Rat.num_pos.mpr hq
  obtain ⟨l,hl,hv⟩ := canonical_cf_exists_fraction q.num.natAbs q.den
    (Int.natAbs_pos.mpr (ne_of_gt hn)) q.pos
  have he : (q.num.natAbs : ℚ)=(q.num : ℚ) := by
    calc
      _ = ((q.num.natAbs : ℤ) : ℚ) := (Int.cast_natCast q.num.natAbs).symm
      _ = (q.num : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg (le_of_lt hn))
  rw [he, q.num_div_den] at hv
  exact ⟨l,⟨hl,hv⟩,fun m hm => canonical_cf_injective hm.1 hl (hm.2.trans hv.symm)⟩

/-- Every actual tree path has one and only one canonical ordinary finite expansion. -/
theorem cw_path_canonical_cf (w : List Bool) :
    ∃! l, CanonicalPositiveCF l ∧ finiteCFValue l=cwValue w :=
  canonical_cf_exists_unique _ (cwValue_positive w)

/-- Conversely, canonical digits reconstruct one and only one actual tree path. -/
theorem canonical_cf_cw_path (l : List ℕ) (hl : CanonicalPositiveCF l) :
    ∃! w, cwValue w=finiteCFValue l :=
  cw_positive_rational_exists_unique _ (canonical_cf_positive hl)

theorem canonical_cf_root : CanonicalPositiveCF [1] ∧ finiteCFValue [1]=cwValue [] := by
  exact ⟨.single 1 le_rfl, by norm_num [finiteCFValue,cwValue]⟩

/-- A run stores its orientation and its number of actual subtraction steps. -/
abbrev OrientedRun := Bool × ℕ

def prependOrientedRun (b : Bool) : List OrientedRun → List OrientedRun
  | [] => [(b,1)]
  | (c,n)::r => if b=c then (c,n+1)::r else (b,1)::(c,n)::r

def orientedRuns : List Bool → List OrientedRun
  | [] => []
  | b::w => prependOrientedRun b (orientedRuns w)

def expandOrientedRuns : List OrientedRun → List Bool
  | [] => []
  | (b,n)::r => List.replicate n b ++ expandOrientedRuns r

/-- Intrinsic maximal-run conditions, not a condition of belonging to an encoder's image. -/
def NormalOrientedRuns : List OrientedRun → Prop
  | [] => True
  | (b,n)::r => 0<n ∧ (∀ p ∈ r.head?, p.1 ≠ b) ∧ NormalOrientedRuns r

theorem expand_prepend_oriented_run (b : Bool) (r : List OrientedRun) :
    expandOrientedRuns (prependOrientedRun b r)=b::expandOrientedRuns r := by
  cases r with
  | nil => rfl
  | cons p r =>
    obtain ⟨c,n⟩ := p
    by_cases h : b=c
    · subst c
      simp [prependOrientedRun,expandOrientedRuns,List.replicate_succ]
    · simp [prependOrientedRun,expandOrientedRuns,h]

theorem expand_oriented_runs (w : List Bool) : expandOrientedRuns (orientedRuns w)=w := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [orientedRuns,expand_prepend_oriented_run,ih]

theorem prepend_oriented_run_normal (b : Bool) {r : List OrientedRun}
    (h : NormalOrientedRuns r) : NormalOrientedRuns (prependOrientedRun b r) := by
  cases r with
  | nil => simp [prependOrientedRun,NormalOrientedRuns]
  | cons p r =>
    obtain ⟨c,n⟩ := p
    by_cases he : b=c
    · subst c
      simp only [prependOrientedRun,if_pos rfl,NormalOrientedRuns] at *
      exact ⟨by omega,h.2⟩
    · simp only [prependOrientedRun,if_neg he,NormalOrientedRuns,List.head?_cons,
        Option.mem_some_iff,forall_eq]
      exact ⟨by omega,by rintro p rfl; exact Ne.symm he,h⟩

theorem oriented_runs_normal (w : List Bool) : NormalOrientedRuns (orientedRuns w) := by
  induction w with
  | nil => trivial
  | cons b w ih => exact prepend_oriented_run_normal b ih

theorem oriented_runs_repeat_append (b : Bool) (n : ℕ) (w : List Bool) (hn : 0<n)
    (h : ∀ p ∈ (orientedRuns w).head?, p.1 ≠ b) :
    orientedRuns (List.replicate n b ++ w)=(b,n)::orientedRuns w := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append,orientedRuns]
    by_cases hn0 : n=0
    · subst n
      simp only [List.replicate_zero,List.nil_append]
      cases he : orientedRuns w with
      | nil => rfl
      | cons p r =>
        obtain ⟨c,k⟩ := p
        have hcb : c ≠ b := h (c,k) (by simp [he])
        simp [prependOrientedRun,Ne.symm hcb]
    · rw [ih (Nat.pos_of_ne_zero hn0)]
      simp [prependOrientedRun]

theorem oriented_runs_expand {r : List OrientedRun} (h : NormalOrientedRuns r) :
    orientedRuns (expandOrientedRuns r)=r := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨b,n⟩ := p
    obtain ⟨hn,hh,hr⟩ := h
    simp only [expandOrientedRuns]
    rw [oriented_runs_repeat_append b n _ hn (by rwa [ih hr]),ih hr]

/-- Two-sided decoding on every intrinsically normalized oriented-run list. -/
def orientedRunEquiv : List Bool ≃ {r : List OrientedRun // NormalOrientedRuns r} where
  toFun w := ⟨orientedRuns w,oriented_runs_normal w⟩
  invFun r := expandOrientedRuns r.val
  left_inv := expand_oriented_runs
  right_inv r := Subtype.ext (oriented_runs_expand r.property)

def canonicalCFPathEquiv : {l : List ℕ // CanonicalPositiveCF l} ≃ List Bool where
  toFun l := Classical.choose (canonical_cf_cw_path l.val l.property)
  invFun w := ⟨Classical.choose (cw_path_canonical_cf w),
    (Classical.choose_spec (cw_path_canonical_cf w)).1.1⟩
  left_inv l := by
    apply Subtype.ext
    apply canonical_cf_injective (Classical.choose_spec (cw_path_canonical_cf _)).1.1 l.property
    exact (Classical.choose_spec (cw_path_canonical_cf _)).1.2.trans
      (Classical.choose_spec (canonical_cf_cw_path l.val l.property)).1
  right_inv w := by
    apply cwValue_injective
    exact (Classical.choose_spec (canonical_cf_cw_path _
      (Classical.choose_spec (cw_path_canonical_cf w)).1.1)).1.trans
      (Classical.choose_spec (cw_path_canonical_cf w)).1.2

theorem canonical_cf_path_value (l : {l : List ℕ // CanonicalPositiveCF l}) :
    cwValue (canonicalCFPathEquiv l)=finiteCFValue l.val :=
  (Classical.choose_spec (canonical_cf_cw_path l.val l.property)).1

def canonicalCFRunEquiv : {l : List ℕ // CanonicalPositiveCF l} ≃
    {r : List OrientedRun // NormalOrientedRuns r} :=
  canonicalCFPathEquiv.trans orientedRunEquiv

/-- `true` subtracts the denominator; `false` subtracts the numerator. -/
def rationalSubtraction (b : Bool) (q : ℚ) : ℚ :=
  if b then q-1 else q/(1-q)

theorem cw_subtraction_step (b : Bool) (w : List Bool) :
    rationalSubtraction b (cwValue (b::w))=cwValue w := by
  have hp := cwValue_positive w
  cases b
  · simp only [rationalSubtraction,Bool.false_eq_true,if_false,cwValue,cwLeft]
    have h0 : 1+cwValue w ≠ 0 := by linarith
    field_simp
  · simp [rationalSubtraction,cwValue,cwRight]

theorem cw_subtraction_orientation (w : List Bool) :
    cwValue (false::w)<1 ∧ 1<cwValue (true::w) :=
  ⟨cwLeft_lt_one (cwValue_positive w),cwRight_gt_one (cwValue_positive w)⟩

theorem cw_right_run_value (n : ℕ) (w : List Bool) :
    cwValue (List.replicate n true ++ w)=n+cwValue w := by
  induction n with
  | zero => simp
  | succ n ih =>
    change 1+cwValue (List.replicate n true ++ w)=(n+1 : ℕ)+cwValue w
    rw [ih]
    push_cast
    ring

theorem cw_complement_value (w : List Bool) :
    cwValue (w.map Bool.not)=(cwValue w)⁻¹ := by
  induction w with
  | nil => norm_num [cwValue]
  | cons b w ih =>
    have h0 := ne_of_gt (cwValue_positive w)
    have h1 : 1+cwValue w ≠ 0 := by linarith [cwValue_positive w]
    cases b <;> simp only [List.map_cons,Bool.not_false,Bool.not_true,cwValue,cwLeft,cwRight,ih]
    · field_simp [h0,h1]; ring
    · field_simp [h0,h1]
      simpa only [add_comm (cwValue w) 1] using div_self h1

theorem cw_left_run_value (n : ℕ) (w : List Bool) :
    cwValue (List.replicate n false ++ w)=(n+(cwValue w)⁻¹)⁻¹ := by
  have h := cw_complement_value (List.replicate n true ++ w.map Bool.not)
  simpa [List.map_append,List.map_replicate,List.map_map,
    Function.comp_def,cw_right_run_value,cw_complement_value] using h

theorem cw_terminal_right_run (n : ℕ) :
    cwValue (List.replicate n true)=(n+1 : ℕ) := by
  simpa only [List.append_nil,cwValue,Nat.cast_add,Nat.cast_one] using cw_right_run_value n []

theorem cw_terminal_left_run (n : ℕ) :
    cwValue (List.replicate n false)=((n+1 : ℕ) : ℚ)⁻¹ := by
  simpa only [List.append_nil,cwValue,inv_one,Nat.cast_add,Nat.cast_one] using cw_left_run_value n []

theorem euclidean_terminal_reduced (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (hab : Nat.Coprime a b) (hr : a%b=0) :
    b=1 ∧ cwValue (List.replicate (a/b-1) true)=(a : ℚ)/b ∧
      (a/b-1)+1=a/b := by
  have hd : b ∣ a := Nat.dvd_of_mod_eq_zero hr
  have hb1 : b=1 := by
    have he := hab.gcd_eq_one
    rw [Nat.gcd_eq_right hd] at he
    exact he
  subst b
  refine ⟨rfl,?_,by simpa using Nat.sub_add_cancel ha⟩
  simp only [Nat.div_one,cw_terminal_right_run,Nat.cast_one,div_one]
  congr 1
  omega

theorem euclidean_root_zero_run :
    orientedRuns ([] : List Bool)=[] ∧ 1/1-1=0 ∧ cwValue []=1 := by
  norm_num [orientedRuns,cwValue]

def subtractWord : List Bool → ℚ → ℚ
  | [], q => q
  | b::w, q => subtractWord w (rationalSubtraction b q)

theorem cw_subtract_prefix (u w : List Bool) :
    subtractWord u (cwValue (u++w))=cwValue w := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    rw [List.cons_append,subtractWord,cw_subtraction_step,ih]

theorem cw_subtract_to_root (w : List Bool) : subtractWord w (cwValue w)=1 := by
  simpa only [List.append_nil,cwValue] using cw_subtract_prefix w []

theorem oriented_runs_head_direction (b : Bool) (w : List Bool) :
    ∀ p ∈ (orientedRuns (b::w)).head?, p.1=b := by
  cases he : orientedRuns w with
  | nil => simp [orientedRuns,he,prependOrientedRun]
  | cons p r =>
    obtain ⟨c,n⟩ := p
    by_cases h : b=c
    · subst c; simp [orientedRuns,he,prependOrientedRun]
    · simp [orientedRuns,he,prependOrientedRun,h]

/-- A nonterminal division produces exactly the quotient's number of right
subtractions, after which the orientation changes. -/
theorem euclidean_right_nonterminal_run (a b : ℕ) (hb : 0<b)
    (hba : b<a) (hr : 0<a%b) :
    ∃ v : List Bool,
      cwValue (false::v)=((a%b : ℕ) : ℚ)/b ∧
      cwValue (List.replicate (a/b) true ++ false::v)=(a : ℚ)/b ∧
      orientedRuns (List.replicate (a/b) true ++ false::v)=
        (true,a/b)::orientedRuns (false::v) ∧
      subtractWord (List.replicate (a/b) true) ((a : ℚ)/b)=((a%b : ℕ) : ℚ)/b := by
  have hp : (0 : ℚ)<((a%b : ℕ) : ℚ)/b := by positivity
  have hu : ((a%b : ℕ) : ℚ)/b<1 := by
    apply (div_lt_one (by positivity : (0 : ℚ)<b)).mpr
    exact_mod_cast Nat.mod_lt a hb
  obtain ⟨w,hw⟩ := cw_positive_rational_exists _ hp
  have hshape : ∃ v, w=false::v := by
    cases w with
    | nil => simp only [cwValue] at hw; linarith
    | cons d v =>
      cases d
      · exact ⟨v,rfl⟩
      · have hg := cwRight_gt_one (cwValue_positive v)
        change 1<cwValue (true::v) at hg
        rw [hw] at hg
        linarith
  obtain ⟨v,rfl⟩ := hshape
  have hval : cwValue (List.replicate (a/b) true ++ false::v)=(a : ℚ)/b := by
    rw [cw_right_run_value,hw]
    simpa only [inv_div] using (finite_cf_division_identity a b hb hr).symm
  refine ⟨v,hw,hval,?_,?_⟩
  · apply oriented_runs_repeat_append
    · exact (Nat.one_le_div_iff hb).mpr (le_of_lt hba)
    · intro p hp
      have he := oriented_runs_head_direction false v p hp
      rw [he]
      decide
  · rw [← hval,cw_subtract_prefix,hw]

/-- The analogous terminal correction when the denominator is the larger entry. -/
theorem euclidean_terminal_left_reduced (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (hab : Nat.Coprime a b) (hr : b%a=0) :
    a=1 ∧ cwValue (List.replicate (b/a-1) false)=(a : ℚ)/b ∧
      (b/a-1)+1=b/a := by
  obtain ⟨ha1,he,hq⟩ := euclidean_terminal_reduced b a hb ha hab.symm hr
  refine ⟨ha1,?_,hq⟩
  rw [ha1,Nat.div_one,cw_terminal_left_run]
  have hb1 : b-1+1=b := by omega
  rw [hb1]
  simp

theorem euclidean_left_nonterminal_run (a b : ℕ) (ha : 0<a)
    (hab : a<b) (hr : 0<b%a) :
    ∃ v : List Bool,
      cwValue (true::v)=(a : ℚ)/((b%a : ℕ) : ℚ) ∧
      cwValue (List.replicate (b/a) false ++ true::v)=(a : ℚ)/b ∧
      orientedRuns (List.replicate (b/a) false ++ true::v)=
        (false,b/a)::orientedRuns (true::v) ∧
      subtractWord (List.replicate (b/a) false) ((a : ℚ)/b)=(a : ℚ)/((b%a : ℕ) : ℚ) := by
  have hp : (0 : ℚ)<(a : ℚ)/((b%a : ℕ) : ℚ) := by positivity
  have hu : (1 : ℚ)<(a : ℚ)/((b%a : ℕ) : ℚ) := by
    apply (one_lt_div (by positivity : (0 : ℚ)<(b%a : ℕ))).mpr
    exact_mod_cast Nat.mod_lt b ha
  obtain ⟨w,hw⟩ := cw_positive_rational_exists _ hp
  have hshape : ∃ v, w=true::v := by
    cases w with
    | nil => simp only [cwValue] at hw; linarith
    | cons d v =>
      cases d
      · have hg := cwLeft_lt_one (cwValue_positive v)
        change cwValue (false::v)<1 at hg
        rw [hw] at hg
        linarith
      · exact ⟨v,rfl⟩
  obtain ⟨v,rfl⟩ := hshape
  have hval : cwValue (List.replicate (b/a) false ++ true::v)=(a : ℚ)/b := by
    rw [cw_left_run_value,hw,← finite_cf_division_identity b a ha hr,inv_div]
  refine ⟨v,hw,hval,?_,?_⟩
  · apply oriented_runs_repeat_append
    · exact (Nat.one_le_div_iff ha).mpr (le_of_lt hab)
    · intro p hp
      have he := oriented_runs_head_direction true v p hp
      rw [he]
      decide
  · rw [← hval,cw_subtract_prefix,hw]

theorem canonical_cf_euclidean_head (a b d : ℕ) (l : List ℕ)
    (h : CanonicalPositiveCF (d::l)) (hv : finiteCFValue (d::l)=(a : ℚ)/b) :
    d=a/b := by
  have he := canonical_cf_head_floor h
  rw [hv,Rat.floor_natCast_div_natCast] at he
  exact_mod_cast he.symm

theorem finite_cf_remove_terminal_one (pre : List ℕ) (c : ℕ) :
    finiteCFValue (pre++[c,1])=finiteCFValue (pre++[c+1]) := by
  induction pre with
  | nil => simp [finiteCFValue]
  | cons a pre ih =>
    change (a : ℚ)+(finiteCFValue (pre++[c,1]))⁻¹=
      a+(finiteCFValue (pre++[c+1]))⁻¹
    rw [ih]

theorem canonical_cf_tail_digits {l : List ℕ} (h : CanonicalCFTail l) :
    l ≠ [] ∧ (∀ a ∈ l, 1 ≤ a) ∧ ∀ a ∈ l.getLast?, 2 ≤ a := by
  induction h with
  | last a ha => simp; omega
  | cons a l ha hl ih =>
    refine ⟨List.cons_ne_nil _ _,?_,?_⟩
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ha
      · exact ih.2.1 d hd
    · cases l with
      | nil => exact False.elim (ih.1 rfl)
      | cons b l => simpa only [List.getLast?_cons_cons] using ih.2.2

theorem canonical_cf_tail_of_digits {l : List ℕ} (hn : l ≠ [])
    (hp : ∀ a ∈ l, 1 ≤ a) (hl : ∀ a ∈ l.getLast?, 2 ≤ a) : CanonicalCFTail l := by
  induction l with
  | nil => exact False.elim (hn rfl)
  | cons a l ih =>
    cases l with
    | nil => exact .last a (hl a (by simp))
    | cons b l =>
      refine .cons a _ (hp a (by simp)) (ih (List.cons_ne_nil _ _) ?_ ?_)
      · intro d hd
        exact hp d (List.mem_cons_of_mem a hd)
      · simpa only [List.getLast?_cons_cons] using hl

theorem canonical_cf_tail_iff_digits (l : List ℕ) :
    CanonicalCFTail l ↔ l ≠ [] ∧ (∀ a ∈ l, 1 ≤ a) ∧ ∀ a ∈ l.getLast?, 2 ≤ a :=
  ⟨canonical_cf_tail_digits,fun h => canonical_cf_tail_of_digits h.1 h.2.1 h.2.2⟩

theorem canonical_positive_cf_iff_digits (l : List ℕ) :
    CanonicalPositiveCF l ↔
      (∃ a : ℕ, 1 ≤ a ∧ l=[a]) ∨
      ∃ a : ℕ, ∃ t : List ℕ, l=a::t ∧ t ≠ [] ∧
        (∀ d ∈ t, 1 ≤ d) ∧ ∀ d ∈ t.getLast?, 2 ≤ d := by
  constructor
  · intro h
    cases h with
    | single a ha => exact Or.inl ⟨a,ha,rfl⟩
    | cons a t ht => exact Or.inr ⟨a,t,rfl,canonical_cf_tail_digits ht⟩
  · rintro (⟨a,ha,rfl⟩ | ⟨a,t,rfl,hn,hp,hl⟩)
    · exact .single a ha
    · exact .cons a t (canonical_cf_tail_of_digits hn hp hl)

theorem rational_subtraction_right_fraction (a b : ℕ) (hb : 0<b) (hba : b<a) :
    rationalSubtraction true ((a : ℚ)/b)=((a-b : ℕ) : ℚ)/b := by
  have h0 : (b : ℚ) ≠ 0 := by positivity
  simp only [rationalSubtraction,if_true,Nat.cast_sub (le_of_lt hba)]
  field_simp

theorem rational_subtraction_left_fraction (a b : ℕ) (ha : 0<a) (hab : a<b) :
    rationalSubtraction false ((a : ℚ)/b)=(a : ℚ)/((b-a : ℕ) : ℚ) := by
  have hb : 0<b := lt_trans ha hab
  have h0 : (b : ℚ) ≠ 0 := by positivity
  have h1 : (b : ℚ)-(a : ℚ) ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hab))
  simp only [rationalSubtraction,Bool.false_eq_true,if_false,Nat.cast_sub (le_of_lt hab)]
  field_simp

end
end Sigma
