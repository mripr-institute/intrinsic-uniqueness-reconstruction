import SigmaThomNativeContext

namespace Sigma
noncomputable section

variable {K H KR HR K' H' KR' HR' : Type*}
  [CommRing K] [CommRing H] [AddCommGroup KR] [AddCommGroup HR]
  [Module K KR] [Module H HR]
  [CommRing K'] [CommRing H'] [AddCommGroup KR'] [AddCommGroup HR']
  [Module K' KR'] [Module H' HR']

/-- Pullbacks on base rings and relative groups, preserving the supplied Thom
classes and commuting with the Chern character. These are naturality data,
not an assumed naturality equation for the unknown correction. -/
structure NativeThomPullback (T : NativeThomContext K H KR HR)
    (U : NativeThomContext K' H' KR' HR') where
  kBase : K →+* K'
  hBase : H →+* H'
  kRelative : KR →+ KR'
  hRelative : HR →+ HR'
  h_smul : ∀ (a : H) (u : HR), hRelative (a • u) = hBase a • hRelative u
  kClass : kRelative T.kClass = U.kClass
  hClass : hRelative T.hClass = U.hClass
  ch : ∀ u, U.chRelative (kRelative u) = hRelative (T.chRelative u)

namespace NativeThomPullback
variable {T : NativeThomContext K H KR HR} {U : NativeThomContext K' H' KR' HR'}

theorem correction_natural (f : NativeThomPullback T U) :
    f.hBase T.correction = U.correction := by
  apply U.correction_unique
  rw [← f.kClass, f.ch, T.correction_comparison, f.h_smul, f.hClass]

end NativeThomPullback

section Line
variable (T : NativeThomContext K H KR HR)

/-- The primitive zero-section data for a complex line: its K-theoretic Euler
class is `1-[L*]`, its cohomological Euler class is `c₁(L)`, and the supplied
Chern character is normalized on the dual line. -/
structure NativeThomLine (u expNeg : H) where
  line : Kˣ
  zeroK : KR →+ K
  zeroH : HR →ₗ[H] H
  zero_ch : ∀ v, T.chBase (zeroK v) = zeroH (T.chRelative v)
  zero_kClass : zeroK T.kClass = 1 - (↑line⁻¹ : K)
  zero_hClass : zeroH T.hClass = u
  ch_dual : T.chBase (↑line⁻¹ : K) = expNeg

/-- The line equation is derived from the zero-section identities and
naturality; it is not an input to the supplied context. -/
theorem native_thom_line_euler {u expNeg : H} (L : NativeThomLine T u expNeg) :
    u * T.correction = 1-expNeg := by
  have h := L.zero_ch T.kClass
  rw [L.zero_kClass, map_sub, map_one, L.ch_dual,
    T.correction_comparison, map_smul, L.zero_hClass] at h
  simpa only [smul_eq_mul, mul_comm] using h.symm

end Line
end
end Sigma
