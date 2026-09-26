import SigmaThomNativeSplitting
import Mathlib.RingTheory.Nilpotent.Basic

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators

theorem thom_stage_variable_nilpotent (n : ℕ) : IsNilpotent (thomStageMap n X) := by
  refine ⟨n+1, ?_⟩
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Constant-one series become one plus a nilpotent at every actual finite
universal cohomology stage. -/
theorem thom_stage_constant_one_nilpotent (n : ℕ) (F : PowerSeries ℚ)
    (hF : constantCoeff ℚ F = 1) : IsNilpotent (thomStageMap n F-1) := by
  have hd : X ∣ F-1 := PowerSeries.X_dvd_iff.mpr (by simp [hF])
  obtain ⟨G,hG⟩ := hd
  rw [← map_one (thomStageMap n), ← map_sub, hG, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_left (thom_stage_variable_nilpotent n)

theorem thom_inverseTodd_constant :
    constantCoeff ℚ (↑(formalToddUnitOver ℚ)⁻¹ : PowerSeries ℚ) = 1 := by
  simp [formalToddUnitOver, todd_denominator_constant]

namespace NativeClassifiedLine
variable {T : SuppliedComplexThomTheory} {U : NativeUniversalBundleTower T}
variable {L : NativeComplexBundle} {hL : T.admissible L}

theorem inverseTodd_evaluation_nilpotent (C : NativeClassifiedLine T U L hL) :
    IsNilpotent (C.evaluate (↑(formalToddUnitOver ℚ)⁻¹ : PowerSeries ℚ)-1) := by
  have h := (thom_stage_constant_one_nilpotent C.stage
    (↑(formalToddUnitOver ℚ)⁻¹ : PowerSeries ℚ) thom_inverseTodd_constant).map
      (C.pullback.hBase.comp (U.coordinate C.stage).symm.toRingHom)
  simpa only [map_sub, map_one] using h

end NativeClassifiedLine

/-- Finite products of one-plus-nilpotent elements remain one-plus-nilpotent. -/
theorem thom_nilpotent_product_sub_one {A ι : Type*} [CommRing A]
    (f : ι → A) (S : Finset ι) (h : ∀ i ∈ S, IsNilpotent (f i-1)) :
    IsNilpotent ((∏ i ∈ S, f i)-1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (show IsNilpotent (0 : A) from ⟨1, by simp⟩)
  | @insert i S hiS ih =>
    rw [Finset.prod_insert hiS]
    have hx := (Commute.all (f i-1) (∏ j ∈ S,f j)).isNilpotent_mul_left
      (h i (Finset.mem_insert_self _ _))
    have hy := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have he : f i * (∏ j ∈ S,f j)-1 =
        (f i-1)*(∏ j ∈ S,f j)+((∏ j ∈ S,f j)-1) := by ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_add hx hy

namespace NativeThomSplit
variable {T : SuppliedComplexThomTheory} {U : NativeUniversalBundleTower T}
variable {V : NativeComplexBundle} {hV : T.admissible V}

theorem root_product_nilpotent (S : NativeThomSplit T U V hV) :
    IsNilpotent (S.inverseToddRootProduct-1) :=
  thom_nilpotent_product_sub_one _ Finset.univ
    (fun i hi => (S.classified i).inverseTodd_evaluation_nilpotent)

/-- Injectivity of the splitting map reflects nilpotence; no extra theorem
asserting that an injective ring map reflects units is used. -/
theorem inverseTodd_nilpotent (S : NativeThomSplit T U V hV) :
    IsNilpotent (S.inverseTodd-1) := by
  apply (IsNilpotent.map_iff S.injective).mp
  rw [map_sub, map_one, S.inverseTodd_spec]
  exact S.root_product_nilpotent

theorem inverseTodd_isUnit (S : NativeThomSplit T U V hV) : IsUnit S.inverseTodd := by
  simpa only [sub_add_cancel] using S.inverseTodd_nilpotent.isUnit_add_one

/-- The independently descended inverse-Todd characteristic class is a unit
on every supplied finite-base splitting context. -/
def inverseToddUnit (S : NativeThomSplit T U V hV) : (T.HBase V.base)ˣ :=
  S.inverseTodd_isUnit.unit

/-- The forward Todd unit is now constructed, rather than assumed. -/
def toddUnit (S : NativeThomSplit T U V hV) : (T.HBase V.base)ˣ := S.inverseToddUnit⁻¹

theorem inverseToddUnit_value (S : NativeThomSplit T U V hV) :
    (S.inverseToddUnit : T.HBase V.base) = S.inverseTodd := S.inverseTodd_isUnit.unit_spec

theorem correction_eq_inverse_toddUnit (S : NativeThomSplit T U V hV) :
    T.correction V hV = (↑S.toddUnit⁻¹ : T.HBase V.base) := by
  rw [toddUnit, inv_inv, S.inverseToddUnit_value, S.correction_eq_inverseTodd]

end NativeThomSplit
end
end Sigma
