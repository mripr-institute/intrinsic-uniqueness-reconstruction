import SigmaRealArithmetic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Sigma
noncomputable section
open scoped Matrix BigOperators

def rationalTreeGenerator (b : Bool) : Matrix (Fin 2) (Fin 2) ℕ :=
  if b then !![1,1;0,1] else !![1,0;1,1]

/-- Head is the outermost transformation, matching cwValue. -/
def rationalTreeMatrix : List Bool → Matrix (Fin 2) (Fin 2) ℕ
  | [] => 1
  | b::w => rationalTreeGenerator b * rationalTreeMatrix w

theorem rational_tree_matrix_left (w : List Bool) :
    rationalTreeMatrix (false::w)=
      !![(rationalTreeMatrix w) 0 0, (rationalTreeMatrix w) 0 1;
         (rationalTreeMatrix w) 0 0+(rationalTreeMatrix w) 1 0,
         (rationalTreeMatrix w) 0 1+(rationalTreeMatrix w) 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalTreeMatrix, rationalTreeGenerator, Matrix.mul_apply, Fin.sum_univ_two]

theorem rational_tree_matrix_right (w : List Bool) :
    rationalTreeMatrix (true::w)=
      !![(rationalTreeMatrix w) 0 0+(rationalTreeMatrix w) 1 0,
         (rationalTreeMatrix w) 0 1+(rationalTreeMatrix w) 1 1;
         (rationalTreeMatrix w) 1 0, (rationalTreeMatrix w) 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalTreeMatrix, rationalTreeGenerator, Matrix.mul_apply, Fin.sum_univ_two]

theorem rational_tree_matrix_cross_determinant (w : List Bool) :
    rationalTreeMatrix w 0 0*rationalTreeMatrix w 1 1=
      rationalTreeMatrix w 0 1*rationalTreeMatrix w 1 0+1 := by
  induction w with
  | nil => norm_num [rationalTreeMatrix]
  | cons b w ih =>
    cases b
    · rw [rational_tree_matrix_left]
      dsimp
      nlinarith
    · rw [rational_tree_matrix_right]
      dsimp
      nlinarith

theorem rational_tree_matrix_positive_rows (w : List Bool) :
    0 < rationalTreeMatrix w 0 0+rationalTreeMatrix w 0 1 ∧
    0 < rationalTreeMatrix w 1 0+rationalTreeMatrix w 1 1 := by
  have h := rational_tree_matrix_cross_determinant w
  constructor <;> nlinarith

theorem rational_tree_matrix_mediant (w : List Bool) :
    ((rationalTreeMatrix w 0 0+rationalTreeMatrix w 0 1:ℕ):ℚ) /
      ((rationalTreeMatrix w 1 0+rationalTreeMatrix w 1 1:ℕ):ℚ)=cwValue w := by
  induction w with
  | nil => norm_num [rationalTreeMatrix,cwValue]
  | cons b w ih =>
    have hp := rational_tree_matrix_positive_rows w
    have hd : ((rationalTreeMatrix w 1 0+rationalTreeMatrix w 1 1:ℕ):ℚ) ≠ 0 := by
      exact_mod_cast hp.2.ne'
    have ht : ((rationalTreeMatrix w 0 0+rationalTreeMatrix w 0 1+
        rationalTreeMatrix w 1 0+rationalTreeMatrix w 1 1:ℕ):ℚ) ≠ 0 := by
      exact_mod_cast (show 0 < rationalTreeMatrix w 0 0+rationalTreeMatrix w 0 1+
        rationalTreeMatrix w 1 0+rationalTreeMatrix w 1 1 by omega).ne'
    cases b
    · rw [rational_tree_matrix_left,cwValue,← ih]
      unfold cwLeft
      dsimp
      push_cast at hd ht ⊢
      field_simp [hd]
      ring_nf
      field_simp [ht]
      ring
    · rw [rational_tree_matrix_right,cwValue,← ih]
      unfold cwRight
      dsimp
      push_cast at hd ⊢
      field_simp
      ring

theorem rational_tree_matrix_injective : Function.Injective rationalTreeMatrix := by
  intro u v h
  apply cwValue_injective
  rw [← rational_tree_matrix_mediant u, ← rational_tree_matrix_mediant v,h]

/-- Every nonidentity determinant-one matrix has a forced row-dominance
direction. The crossed alternative can only be the identity. -/
theorem determinant_one_rows_comparable (a b c d : ℕ) (h : a*d=b*c+1) :
    (a=1 ∧ b=0 ∧ c=0 ∧ d=1) ∨
      (a ≤ c ∧ b ≤ d) ∨ (c ≤ a ∧ d ≤ b) := by
  by_cases hac : a ≤ c
  · by_cases hbd : b ≤ d
    · exact Or.inr (Or.inl ⟨hac,hbd⟩)
    · by_cases hca : c ≤ a
      · exact Or.inr (Or.inr ⟨hca,by omega⟩)
      · have hb : d+1 ≤ b := by omega
        have hc : a+1 ≤ c := by omega
        have hh := Nat.mul_le_mul hb hc
        nlinarith
  · by_cases hdb : d ≤ b
    · exact Or.inr (Or.inr ⟨by omega,hdb⟩)
    · have ha : c+1 ≤ a := by omega
      have hd : b+1 ≤ d := by omega
      have hh := Nat.mul_le_mul ha hd
      have hb0 : b=0 := by nlinarith
      have hc0 : c=0 := by nlinarith
      have had : a*d=1 := by simpa [hb0,hc0] using h
      exact Or.inl ⟨Nat.eq_one_of_dvd_one ⟨d,had.symm⟩,hb0,hc0,
        Nat.eq_one_of_dvd_one ⟨a,by simpa [mul_comm] using had.symm⟩⟩

theorem rational_tree_matrix_generation (a b c d : ℕ) (h : a*d=b*c+1) :
    ∃ w : List Bool, rationalTreeMatrix w=!![a,b;c,d] := by
  generalize hs : a+b+c+d=s
  induction s using Nat.strong_induction_on generalizing a b c d with
  | h s ih =>
    rcases determinant_one_rows_comparable a b c d h with hid | hL | hR
    · rcases hid with ⟨rfl,rfl,rfl,rfl⟩
      exact ⟨[], Matrix.one_fin_two⟩
    · have hdet : a*(d-b)=b*(c-a)+1 := by
        have hc := Nat.sub_add_cancel hL.1
        have hd := Nat.sub_add_cancel hL.2
        nlinarith
      have htop : 0 < a+b := by nlinarith
      have hsize : a+b+(c-a)+(d-b)<s := by omega
      obtain ⟨w,hw⟩ := ih _ hsize a b (c-a) (d-b) hdet rfl
      refine ⟨false::w, ?_⟩
      rw [rational_tree_matrix_left, hw]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Nat.add_sub_of_le, hL.1, hL.2]
    · have hdet : (a-c)*d=(b-d)*c+1 := by
        have ha := Nat.sub_add_cancel hR.1
        have hb := Nat.sub_add_cancel hR.2
        nlinarith
      have hbot : 0 < c+d := by nlinarith
      have hsize : (a-c)+(b-d)+c+d<s := by omega
      obtain ⟨w,hw⟩ := ih _ hsize (a-c) (b-d) c d hdet rfl
      refine ⟨true::w, ?_⟩
      rw [rational_tree_matrix_right, hw]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Nat.sub_add_cancel, hR.1, hR.2]


theorem rational_tree_matrix_append (u v : List Bool) :
    rationalTreeMatrix (u++v)=rationalTreeMatrix u*rationalTreeMatrix v := by
  induction u with
  | nil => simp [rationalTreeMatrix]
  | cons b u ih => simp [rationalTreeMatrix,ih,mul_assoc]

theorem nat_matrix_determinant_one_iff (M : Matrix (Fin 2) (Fin 2) ℕ) :
    (M.map (fun n => (n:ℤ))).det=1 ↔ M 0 0*M 1 1=M 0 1*M 1 0+1 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.map_apply]
  constructor
  · intro h
    have he : (M 0 0:ℤ)*(M 1 1:ℤ)=(M 0 1:ℤ)*(M 1 0:ℤ)+1 := by linarith
    exact_mod_cast he
  · intro h
    have he : (M 0 0:ℤ)*(M 1 1:ℤ)=(M 0 1:ℤ)*(M 1 0:ℤ)+1 := by exact_mod_cast h
    linarith

theorem rational_tree_matrix_determinant (w : List Bool) :
    ((rationalTreeMatrix w).map (fun n => (n:ℤ))).det=1 :=
  (nat_matrix_determinant_one_iff _).mpr (rational_tree_matrix_cross_determinant w)

/-- Native nonnegative integral determinant-one matrices, including identity,
are freely generated by the two displayed native matrices. -/
theorem rational_tree_matrix_exists_unique (M : Matrix (Fin 2) (Fin 2) ℕ)
    (hM : (M.map (fun n => (n:ℤ))).det=1) :
    ∃! w : List Bool, rationalTreeMatrix w=M := by
  obtain ⟨w,hw⟩ := rational_tree_matrix_generation (M 0 0) (M 0 1) (M 1 0) (M 1 1)
    ((nat_matrix_determinant_one_iff M).mp hM)
  have hwm : rationalTreeMatrix w=M := hw.trans (Matrix.eta_fin_two M).symm
  exact ⟨w,hwm,fun v hv => rational_tree_matrix_injective (hv.trans hwm.symm)⟩

/-- Chronological paths apply their first letter first. -/
def chronologicalCwValue (w : List Bool) : ℚ := cwValue w.reverse

def sternBrocotMatrix (w : List Bool) : Matrix (Fin 2) (Fin 2) ℕ :=
  rationalTreeMatrix w

def sternBrocotValue (w : List Bool) : ℚ :=
  ((sternBrocotMatrix w 0 0+sternBrocotMatrix w 0 1:ℕ):ℚ) /
    ((sternBrocotMatrix w 1 0+sternBrocotMatrix w 1 1:ℕ):ℚ)

theorem chronological_cw_left (w : List Bool) :
    chronologicalCwValue (w++[false])=cwLeft (chronologicalCwValue w) := by
  simp [chronologicalCwValue,List.reverse_append,cwValue]

theorem chronological_cw_right (w : List Bool) :
    chronologicalCwValue (w++[true])=cwRight (chronologicalCwValue w) := by
  simp [chronologicalCwValue,List.reverse_append,cwValue]

theorem stern_brocot_right_step (w : List Bool) (b : Bool) :
    sternBrocotMatrix (w++[b])=sternBrocotMatrix w*rationalTreeGenerator b := by
  simp [sternBrocotMatrix,rational_tree_matrix_append,rationalTreeMatrix]

theorem stern_brocot_left_columns (w : List Bool) :
    sternBrocotMatrix (w++[false])=
      !![sternBrocotMatrix w 0 0+sternBrocotMatrix w 0 1,sternBrocotMatrix w 0 1;
         sternBrocotMatrix w 1 0+sternBrocotMatrix w 1 1,sternBrocotMatrix w 1 1] := by
  rw [stern_brocot_right_step]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalTreeGenerator,Matrix.mul_apply,Fin.sum_univ_two]

theorem stern_brocot_right_columns (w : List Bool) :
    sternBrocotMatrix (w++[true])=
      !![sternBrocotMatrix w 0 0,sternBrocotMatrix w 0 0+sternBrocotMatrix w 0 1;
         sternBrocotMatrix w 1 0,sternBrocotMatrix w 1 0+sternBrocotMatrix w 1 1] := by
  rw [stern_brocot_right_step]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalTreeGenerator,Matrix.mul_apply,Fin.sum_univ_two]

theorem stern_brocot_cw_reversal (w : List Bool) :
    sternBrocotValue w=chronologicalCwValue w.reverse := by
  simpa [sternBrocotValue,sternBrocotMatrix,chronologicalCwValue] using
    rational_tree_matrix_mediant w

theorem chronological_cw_LR : chronologicalCwValue [false,true]=3/2 := by
  norm_num [chronologicalCwValue,cwValue,cwLeft,cwRight]

theorem stern_brocot_LR : sternBrocotValue [false,true]=2/3 := by
  rw [stern_brocot_cw_reversal]
  norm_num [chronologicalCwValue,cwValue,cwLeft,cwRight]

theorem stern_brocot_enumeration (q : ℚ) (hq : 0 < q) :
    ∃! w : List Bool, sternBrocotValue w=q := by
  simpa only [sternBrocotValue,sternBrocotMatrix,rational_tree_matrix_mediant] using
    cw_positive_rational_exists_unique q hq

theorem determinant_one_mediant_coprime (a b c d : ℕ) (h : a*d=b*c+1) :
    Nat.Coprime (a+b) (c+d) := by
  change Nat.gcd (a+b) (c+d)=1
  apply Nat.eq_one_of_dvd_one
  have h₁ : Nat.gcd (a+b) (c+d) ∣ (a+b)*d :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
  have h₂ : Nat.gcd (a+b) (c+d) ∣ b*(c+d) :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
  have he : (a+b)*d=b*(c+d)+1 := by nlinarith
  rw [he] at h₁
  exact (Nat.dvd_add_iff_left h₂).mpr (by simpa [add_comm] using h₁)

theorem stern_brocot_mediant_reduced (w : List Bool) :
    Nat.Coprime (sternBrocotMatrix w 0 0+sternBrocotMatrix w 0 1)
      (sternBrocotMatrix w 1 0+sternBrocotMatrix w 1 1) :=
  determinant_one_mediant_coprime _ _ _ _ (rational_tree_matrix_cross_determinant w)

/-- Infinity is allowed only at the upper endpoint. The exact determinant
identity supplies adjacency even in that endpoint case. -/
theorem stern_brocot_endpoint_order (w : List Bool) :
    0 < sternBrocotMatrix w 1 1 ∧
      (sternBrocotMatrix w 1 0=0 ∨
        (sternBrocotMatrix w 0 1:ℚ)/sternBrocotMatrix w 1 1 <
          (sternBrocotMatrix w 0 0:ℚ)/sternBrocotMatrix w 1 0) := by
  have h := rational_tree_matrix_cross_determinant w
  change sternBrocotMatrix w 0 0*sternBrocotMatrix w 1 1=
    sternBrocotMatrix w 0 1*sternBrocotMatrix w 1 0+1 at h
  have hd : 0 < sternBrocotMatrix w 1 1 := by nlinarith
  refine ⟨hd,?_⟩
  by_cases hc : sternBrocotMatrix w 1 0=0
  · exact Or.inl hc
  · right
    apply (div_lt_div_iff₀ (by exact_mod_cast hd)
      (by exact_mod_cast Nat.pos_of_ne_zero hc)).mpr
    exact_mod_cast (show sternBrocotMatrix w 0 1*sternBrocotMatrix w 1 0 <
      sternBrocotMatrix w 0 0*sternBrocotMatrix w 1 1 by omega)



theorem nonnegative_integer_matrix_exists_unique (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hpos : ∀ i j, 0 ≤ M i j) (hdet : M.det=1) :
    ∃! w : List Bool, (rationalTreeMatrix w).map (fun n => (n:ℤ))=M := by
  let N : Matrix (Fin 2) (Fin 2) ℕ := M.map Int.toNat
  have hN : N.map (fun n => (n:ℤ))=M := by
    ext i j
    exact Int.toNat_of_nonneg (hpos i j)
  obtain ⟨w,hw,huniq⟩ := rational_tree_matrix_exists_unique N (by rw [hN]; exact hdet)
  refine ⟨w, ?_, ?_⟩
  · change (rationalTreeMatrix w).map (fun n => (n:ℤ))=M
    rw [hw,hN]
  intro v hv
  apply huniq
  ext i j
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => (A i j).toNat) hv
  simpa [N,Matrix.map_apply] using h

def sternBrocotLower (w : List Bool) : ℚ :=
  (sternBrocotMatrix w 0 1:ℚ)/sternBrocotMatrix w 1 1

def sternBrocotUpper (w : List Bool) : WithTop ℚ :=
  if sternBrocotMatrix w 1 0=0 then ⊤ else
    ↑((sternBrocotMatrix w 0 0:ℚ)/sternBrocotMatrix w 1 0)

theorem stern_brocot_ordered_endpoints (w : List Bool) :
    (sternBrocotLower w : WithTop ℚ) < sternBrocotUpper w := by
  obtain ⟨_,h⟩ := stern_brocot_endpoint_order w
  by_cases hc : sternBrocotMatrix w 1 0=0
  · simp [sternBrocotUpper,hc]
  · rw [sternBrocotUpper,if_neg hc]
    exact_mod_cast h.resolve_left hc

theorem stern_brocot_initial_endpoints :
    sternBrocotUpper []=⊤ ∧ sternBrocotLower []=0 ∧ sternBrocotValue []=1 := by
  norm_num [sternBrocotUpper,sternBrocotLower,sternBrocotValue,
    sternBrocotMatrix,rationalTreeMatrix]


end
end Sigma
