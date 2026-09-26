import SigmaThomNativeGysin

namespace Sigma
noncomputable section

variable {K H KR HR KS HS KRS HRS : Type*}
  [CommRing K] [CommRing H] [AddCommGroup KR] [AddCommGroup HR]
  [Module K KR] [Module H HR]
  [AddCommGroup KS] [AddCommGroup HS] [AddCommGroup KRS] [AddCommGroup HRS]
  [Module K KS] [Module H HS] [Module K KRS] [Module H HRS]

/-- Supported source classes are modules, not unital rings. The supported Thom
maps are cup product with the ordinary Thom classes. Compatibility of Chern
character is supplied on primitive cup products; no correction formula is a field. -/
structure NativeSupportedThom (T : NativeThomContext K H KR HR) where
  chSource : KS →+ HS
  chRelative : KRS →+ HRS
  kCup : KS →ₗ[K] KR →ₗ[K] KRS
  hCup : HS →ₗ[H] HR →ₗ[H] HRS
  ch_cup : ∀ a u, chRelative (kCup a u) = hCup (chSource a) (T.chRelative u)
  kThom : KS ≃ₗ[K] KRS
  hThom : HS ≃ₗ[H] HRS
  kThom_apply : ∀ a, kThom a = kCup a T.kClass
  hThom_apply : ∀ a, hThom a = hCup a T.hClass

namespace NativeSupportedThom
variable {T : NativeThomContext K H KR HR}
variable (S : NativeSupportedThom (KS := KS) (HS := HS) (KRS := KRS) (HRS := HRS) T)

/-- Thom comparison for arbitrary supported source classes, derived from the
ordinary Thom correction and the bilinear cup-product identities. -/
theorem comparison (a : KS) :
    S.chRelative (S.kThom a) = S.hThom (T.correction • S.chSource a) := by
  rw [S.kThom_apply, S.ch_cup, T.correction_comparison, map_smul,
    S.hThom_apply, LinearMap.map_smul, LinearMap.smul_apply]

variable {KY HY : Type*} [AddCommGroup KY] [AddCommGroup HY]

/-- Compatible support-preserving collapse/transport maps, with arbitrary
supported target groups. Neither source nor target is required to be a ring. -/
structure Collapse where
  kMap : KRS →+ KY
  hMap : HRS →+ HY
  chTarget : KY →+ HY
  ch_natural : ∀ u, chTarget (kMap u) = hMap (S.chRelative u)

namespace Collapse
variable {S} (C : S.Collapse (KY := KY) (HY := HY))

def kGysin : KS →+ KY := C.kMap.comp S.kThom.toAddMonoidHom
def hGysin : HS →+ HY := C.hMap.comp S.hThom.toAddMonoidHom

theorem comparison (a : KS) :
    C.chTarget (C.kGysin a) = C.hGysin (T.correction • S.chSource a) := by
  change C.chTarget (C.kMap (S.kThom a)) = C.hMap (S.hThom _)
  rw [C.ch_natural, S.comparison]

/-- The supported Riemann--Roch identity after identifying the ordinary normal
Todd class. Correction still acts on the supported cohomology module. -/
theorem normal_riemann_roch (tdNormal : Hˣ)
    (hNormal : T.correction = (↑tdNormal⁻¹ : H)) (a : KS) :
    C.chTarget (C.kGysin a) = C.hGysin ((↑tdNormal⁻¹ : H) • S.chSource a) := by
  rw [C.comparison, hNormal]

theorem stable_tangent_riemann_roch {G : Type*} [AddCommGroup G]
    (td : Multiplicative G →* Hˣ) (normal stable tangent : G)
    (hTangent : tangent = stable-normal) (hStable : td (Multiplicative.ofAdd stable) = 1)
    (hNormal : T.correction = (↑(td (Multiplicative.ofAdd normal))⁻¹ : H)) (a : KS) :
    C.chTarget (C.kGysin a) =
      C.hGysin ((↑(td (Multiplicative.ofAdd tangent)) : H) • S.chSource a) := by
  rw [C.comparison, hNormal, hTangent]
  have he : td (Multiplicative.ofAdd (stable-normal)) =
      (td (Multiplicative.ofAdd normal))⁻¹ := by
    change td (Multiplicative.ofAdd stable / Multiplicative.ofAdd normal) = _
    rw [map_div, hStable, one_div]
  rw [he]

end Collapse
end NativeSupportedThom
end
end Sigma
